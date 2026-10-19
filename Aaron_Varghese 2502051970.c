/
 * ---------------------------------------
 * Routers are vertices, links are edges, link cost is the edge weight.
 *
 * Build:  gcc -Wall -Wextra -o routing_lab_simple routing_lab_simple.c
 *
 *
 * Parts
 *   1. Dijkstra with a min-heap    (link-state routing, like OSPF)
 *   2. Distance-vector routing     (Bellman-Ford idea)
 *   3. Prim's spanning tree
 *   4. Link failure and re-routing
 */

#include <stdio.h>

#define N   6          /* number of routers: A, B, C, D, E, F */
#define INF 999999

/* Adjacency matrix: graph[a][b] = cost of link a-b, 0 means no link */
int graph[N][N];

void add_link(int a, int b, int cost) {
    graph[a][b] = cost;
    graph[b][a] = cost;
}

void remove_link(int a, int b) {
    graph[a][b] = 0;
    graph[b][a] = 0;
}

/* ------------------------------------------------------------------
 * Min-heap (priority queue): the smallest dist is always at heap[0]
 * ------------------------------------------------------------------ */
typedef struct {
    int dist;
    int node;
} HeapItem;

HeapItem heap[100];
int heap_size = 0;

void swap(HeapItem *a, HeapItem *b) {
    HeapItem temp = *a;
    *a = *b;
    *b = temp;
}

void heap_push(int dist, int node) {
    int i = heap_size++;
    heap[i].dist = dist;
    heap[i].node = node;
    /* move up while smaller than the parent */
    while (i > 0 && heap[(i - 1) / 2].dist > heap[i].dist) {
        swap(&heap[i], &heap[(i - 1) / 2]);
        i = (i - 1) / 2;
    }
}

HeapItem heap_pop() {
    HeapItem top = heap[0];
    heap[0] = heap[--heap_size];
    int i = 0;
    /* move down while bigger than a child */
    while (1) {
        int left = 2 * i + 1, right = 2 * i + 2, smallest = i;
        if (left < heap_size && heap[left].dist < heap[smallest].dist)
            smallest = left;
        if (right < heap_size && heap[right].dist < heap[smallest].dist)
            smallest = right;
        if (smallest == i) break;
        swap(&heap[i], &heap[smallest]);
        i = smallest;
    }
    return top;
}

/* ------------------------------------------------------------------
 * Part 1: Dijkstra
 * dist[v] = shortest cost from src to v
 * prev[v] = router just before v on that shortest path
 * ------------------------------------------------------------------ */
void dijkstra(int src, int dist[], int prev[]) {
    for (int i = 0; i < N; i++) {
        dist[i] = INF;
        prev[i] = -1;
    }
    dist[src] = 0;
    heap_size = 0;
    heap_push(0, src);

    while (heap_size > 0) {
        HeapItem top = heap_pop();
        int u = top.node;

        if (top.dist > dist[u]) continue;   /* old entry, skip it */

        for (int v = 0; v < N; v++) {
            if (graph[u][v] == 0) continue;           /* no link u-v */
            int new_dist = dist[u] + graph[u][v];
            if (new_dist < dist[v]) {                 /* found a shorter path */
                dist[v] = new_dist;
                prev[v] = u;
                heap_push(new_dist, v);
            }
        }
    }
}


int first_hop(int prev[], int src, int dest) {
    int x = dest;
    while (prev[x] != src)
        x = prev[x];
    return x;
}

void print_routing_table(int src) {
    int dist[N], prev[N];
    dijkstra(src, dist, prev);

    printf("Routing table for router %c:\n", 'A' + src);
    printf("  Dest  Next hop  Cost\n");
    for (int d = 0; d < N; d++) {
        if (d == src || dist[d] == INF) continue;
        printf("  %c     %c         %d\n", 'A' + d, 'A' + first_hop(prev, src, d), dist[d]);
    }
}

/* Send a packet hop by hop. Each router looks at its own table. */
void forward_packet(int src, int dest) {
    int dist[N], prev[N];
    int current = src;

    printf("Packet %c -> %c: %c", 'A' + src, 'A' + dest, 'A' + src);
    while (current != dest) {
        dijkstra(current, dist, prev);
        if (dist[dest] == INF) {
            printf("  (no route!)\n");
            return;
        }
        current = first_hop(prev, current, dest);
        printf(" -> %c", 'A' + current);
    }
    printf("  (delivered)\n");
}

/* ------------------------------------------------------------------
 * Part 2: Distance-vector routing
 * Each router keeps a table of costs and only learns from its neighbors.
 * Every round, a router checks: "is going through my neighbor cheaper?"
 * Returns the number of rounds that changed something.
 * ------------------------------------------------------------------ */

int distance_vector(int dv[N][N], int next[N][N]) {
    for (int r = 0; r < N; r++) {
        for (int d = 0; d < N; d++) {
            dv[r][d] = (r == d) ? 0 : INF;
            next[r][d] = -1;
        }
    }

    int rounds = 0;
    int changed = 1;
    while (changed) {
        changed = 0;

        /* copy the tables so everyone uses last round's values */
        int old[N][N];
        for (int r = 0; r < N; r++)
            for (int d = 0; d < N; d++)
                old[r][d] = dv[r][d];

        for (int r = 0; r < N; r++) {
            for (int nbr = 0; nbr < N; nbr++) {
                if (graph[r][nbr] == 0) continue;      /* not a neighbor */
                for (int d = 0; d < N; d++) {
                    if (old[nbr][d] == INF) continue;
                    int cost = graph[r][nbr] + old[nbr][d];
                    if (cost < dv[r][d]) {
                        dv[r][d] = cost;
                        next[r][d] = nbr;
                        changed = 1;
                    }
                }
            }
        }
        if (changed) rounds++;
    }
    return rounds;
}

/* ------------------------------------------------------------------
 * Part 3: Prim's minimum spanning tree
 * Grow a tree from start, always adding the cheapest link to a new router.
 * parent[v] = router that connects v to the tree. Returns total cost.
 * ------------------------------------------------------------------ */

int prim(int start, int parent[]) {
    int in_tree[N] = {0};
    int key[N];             /* cheapest link cost to reach each router */
    int total = 0;

    for (int i = 0; i < N; i++) {
        key[i] = INF;
        parent[i] = -1;
    }
    key[start] = 0;

    for (int count = 0; count < N; count++) {
      
        int u = -1;
        for (int v = 0; v < N; v++)
            if (!in_tree[v] && (u == -1 || key[v] < key[u]))
                u = v;

        in_tree[u] = 1;
        total += key[u];

        /* update keys of the neighbors */
        for (int v = 0; v < N; v++) {
            if (graph[u][v] != 0 && !in_tree[v] && graph[u][v] < key[v]) {
                key[v] = graph[u][v];
                parent[v] = u;
            }
        }
    }
    return total;
}

/* ------------------------------------------------------------------
 * Main
 * ------------------------------------------------------------------ */


int main(void) {
    /* Build the network: routers A=0 B=1 C=2 D=3 E=4 F=5 */
    add_link(0, 1, 4);    /* A-B */
    add_link(0, 2, 2);    /* A-C */
    add_link(1, 2, 1);    /* B-C */
    add_link(1, 3, 5);    /* B-D */
    add_link(2, 3, 8);    /* C-D */
    add_link(2, 4, 10);   /* C-E */
    add_link(3, 4, 2);    /* D-E */
    add_link(3, 5, 6);    /* D-F */
    add_link(4, 5, 3);    /* E-F */

    int dist[N], prev[N];
    int dv[N][N], next[N][N];
    int parent[N];

    printf("=== PART 1: Dijkstra (link-state) ===\n");
    print_routing_table(0);
    forward_packet(0, 5);

    printf("\n=== PART 2: Distance-vector ===\n");
    int rounds = distance_vector(dv, next);
    printf("Converged after %d rounds.\n", rounds);
    printf("Router A's table:\n");
    for (int d = 1; d < N; d++)
        printf("  to %c: next hop %c, cost %d\n", 'A' + d, 'A' + next[0][d], dv[0][d]);

    dijkstra(0, dist, prev);
    int same = 1;
    for (int d = 0; d < N; d++)
        if (dv[0][d] != dist[d]) same = 0;
    printf("Same costs as Dijkstra? %s\n", same ? "yes" : "no");

    printf("\n=== PART 3: Minimum spanning tree (Prim) ===\n");
    int total = prim(0, parent);
    for (int v = 1; v < N; v++)
        printf("  %c - %c  (cost %d)\n", 'A' + parent[v], 'A' + v, graph[parent[v]][v]);
    printf("Total cost: %d\n", total);

    printf("\n=== PART 4: Link B-C fails ===\n");
    remove_link(1, 2);
    print_routing_table(0);
    forward_packet(0, 5);
    rounds = distance_vector(dv, next);
    printf("Distance-vector reconverged in %d rounds.\n", rounds);

    return 0;
}
