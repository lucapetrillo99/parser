#include <stdio.h>
#include <stdbool.h>

typedef struct node {
    struct node *next;
    int val1, val2;
    double x, y;
    bool black;
} node;

void insert_value(node *root, int val) {
    node *p, *q;
    int a, b, c;
    p = q;
    a = b + c;
    while (p == q) {
        q = NULL;
        a++;
        if (a > 2) {
            b++;
        } else {
            c = 0;
            return;
        }
        q = p;
    }
    q = NULL;
    return;
}

void delete_value(node *ptr1, node *ptr2) {
    int b;
    bool cond1;
    bool cond2;
    bool cond3;

    cond1 = (ptr1 != NULL);
    cond2 = (ptr2 != NULL);
    cond3 = cond1 || cond2;

    while (cond3) {
        ptr1->x = 0.1;
        if (b > 0) {
            b++;
        } else {
            b = 0;
        }
    }

    return;
}
