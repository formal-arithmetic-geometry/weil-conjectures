## What changed

Proved `WeilConjectures.integralExceptionalSiteDerivedInverse_existsUnique` by
full faithfulness of precomposition with the derived localization. The ordinary
inverse comparison and the specified factorization isomorphisms give exactly the
required square on every complex. Localization also gives uniqueness. Both
categorical helpers are private and proved. Public signatures, definitions and
public imports are unchanged. A private proof import supplies the exact-derived
factorization API without changing what importers see.

Updated the existing node's proof, proof dependencies and proof origin. The direct
comparison remains its original named theorem with its original proof hole. A
candidate proof using K-injective derivability was explored but not delivered:
its concrete normalization did not compile within the fixed limit.

## Proved and sorry left

Closed one of the two original holes:

- `WeilConjectures.integralExceptionalSiteDerivedInverse_existsUnique`.

One original hole remains, attached to `def-pur-adic-derived-site-realization`:

- `WeilConjectures.integralExceptionalSiteDerivedRight_existsUnique`.

No holes added and no split-off statements. The remaining declaration retains its
source and complete proof in words. This is a partial delivery for a module with
several holes; the direct-comparison hole is untouched.

## No longer needed

None. No original import, node, module or declaration was removed. The private
proof import is used only by the inverse proof. The unit's statement and realized
proof steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps or proof dependencies. Its theorem docstrings
supplied the exact-localization and K-injective arguments. The proved inverse-image
part is now recorded in the node; the direct-image argument remains to be checked.
No mathematical statement or definition repair was needed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
