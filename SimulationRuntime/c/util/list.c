/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2014, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF THE BSD NEW LICENSE OR THE
 * GPL VERSION 3 LICENSE OR THE OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the OSMC (Open Source Modelica Consortium)
 * Public License (OSMC-PL) are obtained from OSMC, either from the above
 * address, from the URLs: http://www.openmodelica.org or
 * http://www.ida.liu.se/projects/OpenModelica, and in the OpenModelica
 * distribution. GNU version 3 is obtained from:
 * http://www.gnu.org/copyleft/gpl.html. The New BSD License is obtained from:
 * http://www.opensource.org/licenses/BSD-3-Clause.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, EXCEPT AS
 * EXPRESSLY SET FORTH IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE
 * CONDITIONS OF OSMC-PL.
 *
 */

/*! \file list.c
 *
 * Description: This file is a C header file for the simulation runtime.
 * It contains a simple linked list
 */

#include "list.h"
#include "omc_error.h"

#include <memory.h>
#include <stdlib.h>

struct LIST_NODE
{
  void *data;
  LIST_NODE *next;
};

struct LIST
{
  LIST_NODE *first;
  LIST_NODE *last;
  unsigned int itemSize;
  unsigned int length;
};

LIST *allocList(unsigned int itemSize)
{
  LIST *list = (LIST*)malloc(sizeof(LIST));
  assertStreamPrint(NULL, 0 != list, "out of memory");

  list->first = NULL;
  list->last = NULL;
  list->itemSize = itemSize;
  list->length = 0;

  return list;
}

void freeList(LIST *list)
{
  if(list)
  {
    listClear(list);
    free(list);
  }
}

void listPushFront(LIST *list, void *data)
{
  LIST_NODE *tmpNode = NULL;
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");

  tmpNode = (LIST_NODE*)malloc(sizeof(LIST_NODE));
  assertStreamPrint(NULL, 0 != tmpNode, "out of memory");

  tmpNode->data = malloc(list->itemSize);
  assertStreamPrint(NULL, 0 != tmpNode->data, "out of memory");

  memcpy(tmpNode->data, data, list->itemSize);
  tmpNode->next = list->first;
  ++(list->length);

  list->first = tmpNode;
  if(!list->last)
    list->last = list->first;
}

void listPushBack(LIST *list, void *data)
{
  LIST_NODE *tmpNode = NULL;
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");

  tmpNode = (LIST_NODE*)malloc(sizeof(LIST_NODE));
  assertStreamPrint(NULL, 0 != tmpNode, "out of memory");

  tmpNode->data = malloc(list->itemSize);
  assertStreamPrint(NULL, 0 != tmpNode->data, "out of memory");

  memcpy(tmpNode->data, data, list->itemSize);
  tmpNode->next = NULL;
  ++(list->length);

  if(list->last)
    list->last->next = tmpNode;

  list->last = tmpNode;

  if(!list->first)
    list->first = list->last;
}

int listLen(LIST *list)
{
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");
  return list->length;
}

void *listFirstData(LIST *list)
{
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");
  assertStreamPrint(NULL, 0 != list->first, "empty list");
  return list->first->data;
}

void *listLastData(LIST *list)
{
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");
  assertStreamPrint(NULL, 0 != list->last, "empty list");
  return list->last->data;
}

void listPopFront(LIST *list)
{
  if(list)
  {
    if(list->first)
    {
      LIST_NODE *tmpNode = list->first->next;
      free(list->first->data);
      free(list->first);

      list->first = tmpNode;
      --(list->length);
      if(!list->first)
        list->last = list->first;
    }
  }
}

void listClear(LIST *list)
{
  LIST_NODE *delNode;

  if(!list)
    return;

  delNode = list->first;
  while(delNode)
  {
    LIST_NODE *tmpNode = delNode->next;
    free(delNode->data);
    free(delNode);
    delNode = tmpNode;
  }

  list->length = 0;
  list->first = NULL;
  list->last = NULL;
}

LIST_NODE *listFirstNode(LIST *list)
{
  assertStreamPrint(NULL, 0 != list, "invalid list-pointer");
  assertStreamPrint(NULL, 0 != list->first, "invalid fist list-pointer");
  return list->first;
}

LIST_NODE *listNextNode(LIST_NODE *node)
{
  assertStreamPrint(NULL, 0 != node, "invalid list-node");
  if(node)
    return node->next;
  return NULL;
}

void *listNodeData(LIST_NODE *node)
{
  assertStreamPrint(NULL, 0 != node, "invalid list-node");
  assertStreamPrint(NULL, 0 != node->data, "invalid data node");
  return node->data;
}
