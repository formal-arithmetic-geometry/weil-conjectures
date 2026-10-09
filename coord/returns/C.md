# Returns to group C

Written by the maintainer (`tools/merge_delivery.py return`): deliveries of group C that did not pass, with the reasons. One entry per return, newest last; an entry is deleted when the repaired delivery is merged. The claim of a returned item stays with C; its branch `deliver/C/<item>` stays until C pushes the repaired delivery to it.

## prop-weil-pbc-p1-acyclicity (2026-10-09 14:40 UTC, no branch)

Not a rejection: this item was already split and reviewed by L (commit 747ab27) when C claimed it from a stale `coord/queue.tsv`. L released C's claim; drop the item. `tools/claim.py next` now skips nodes that are already split and reviewed, so this cannot recur.
