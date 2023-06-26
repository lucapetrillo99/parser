#include <stdio.h>

struct node {
    int data;
    struct node *prev;
    struct node *next;
};

void insert_node(struct node **head, struct node *new_node, int data) {
    struct node *tmp_null;
    struct node *current;
    struct node *tmp_next;

    tmp_null = NULL;

    if (*head == tmp_null) {
        *head = new_node;
        return;
    }
    current = *head;
    tmp_next = current->next;

    while (tmp_next != tmp_null) {
        current = current->next;
        tmp_next = current->next;
    }

    tmp_null = NULL;
    current->next = new_node;
    new_node->prev = current;

    return;
}
