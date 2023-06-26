#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

typedef struct node {
    struct node *next;
    int val1, val2;
    double x, y;
    bool black;
};

struct node *new_node;
int a = 10;
#define A 0

void insert_value(struct node *root, int val) {
    struct node *p, *q;
    int a, b, c;
    p = q;
    a = b + c;
    while (p == q) {
        q = NULL;
        a++;
        if (a > 2) {
            b++;
        } else {
            c = A;
            return;
        }
        q = p;
    }
    q = NULL;

    delete_value();
    return;
}
