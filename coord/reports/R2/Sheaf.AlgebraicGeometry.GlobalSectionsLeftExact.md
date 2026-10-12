## What changed

Proved `AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor_additive_leftExact`
in `lean/Sheaf/AlgebraicGeometry/GlobalSectionsLeftExact.lean`, with the original
signature and definition unchanged. Unfolding the functor exposes sectionwise
addition, so additivity is `rfl`. For kernel preservation, explicitly instantiate
Mathlib's limit preservation for `toPresheaf X` and for evaluation at the top open;
composition then supplies preservation of `parallelPair f 0` by typeclass inference.
Only the original `Mathlib.AlgebraicGeometry.Modules.Sheaf` public import is needed;
the second reading removed the unused `Mathlib.CategoryTheory.Preadditive.LeftExact`.
Updated the node's proof and proof dependencies to match this direct argument.

## Proved and sorry left

Proved the module's sole sorry:
`AlgebraicGeometry.Scheme.Modules.globalSectionsFunctor_additive_leftExact`
(node `lem-sc-global-sections-left-exact`). No sorry remains, and none was added.
Local compilation passes without warnings. The delivery dry run checks all
axioms and compilation on the server as well.

## No longer needed

Removed the unused original public import
`Mathlib.CategoryTheory.Preadditive.LeftExact`: the retained scheme-module import
already exposes every declaration used in the signatures and proof. No additional
Sheaf or WeilConjectures module is needed. The attempted proof-only import
`Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory` was removed after checking
that the original imports already expose the required instances.
`def-sp-left-exact-additive` is no longer a proof dependency: the proof constructs
Mathlib's Additive class directly rather than deriving it through preservation of
finite products. It remains a statement dependency explaining the terminology,
and its blueprint unit is not bypassed. The other two original proof dependencies
remain: the module-sheaf definition and sectionwise limits.
No unit statement or proof step is bypassed (the item's unit has no realized node
attached to this item). No entire original dependency module is pruned.

## Where the brief, the DAG or earlier work was wrong

The planned derivation of additivity from finite products is unnecessary here:
addition of section maps is definitionally sectionwise. Mathlib already supplies
the full limit-preservation result for the exact scheme forgetful functor used by
this definition (Modules/Sheaf.lean:78). Explicit local preservation instances
resolve the universe inference that initially prevented the composition instance
from being found. No mathematical statement or public interface was changed.
The argument is uniform in the scheme; it adds no nonemptiness hypothesis and
also applies to the empty scheme and to zero morphisms.


## Second reading by R2

1. Compared the sole delivered module against the repository with `diff -u`.
   The definition body, universe, theorem signature, and all docstrings are byte
   for byte unchanged. The worker changed only the theorem proof; my additional
   change removes an unused import. No new statement is needed. The import cleanup is documented in
   `coord/changes/GlobalSectionsLeftExactImports.md`, as preflight requires.
2. Independently compiled the module with `lcompile.py`, then compiled a scratch
   copy with `#print axioms` for both `globalSectionsFunctor` and
   `globalSectionsFunctor_additive_leftExact`. Both use only `propext`,
   `Classical.choice`, and `Quot.sound`. No sorry or forbidden declaration remains.
   Read Mathlib's `Scheme.Modules.toPresheaf` definition and its preservation
   instance (Modules/Sheaf.lean:78), and `evaluationPreservesLimits`
   (Limits/FunctorCategory/Basic.lean:405). The composition preserves the equalizer
   of `(f, 0)`, exactly the stated kernel clause. The additive constructor is
   sectionwise `map_add` by definitional equality, with no extra hypothesis on X.
3. There are no split-off statements, new declarations, or new nodes to validate.
   Searched the library and Mathlib for global-sections and additive-section
   declarations; ringed-space sections land in ModuleCat and the pro-etale
   sections functor concerns a different site, so neither shortens this proof.
   Empty schemes and zero morphisms remain covered by the general instances.
4. The proof takes the direct Mathlib route and needs no open library theorem.
   Every old proof dependency is accounted for: the category definition and
   sectionwise limits remain, while `def-sp-left-exact-additive` is pruned from
   proof dependencies and retained in statement dependencies. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement and step lists
   are empty, and this item realizes no fixed unit step. No unit route is bypassed.
   Tested removal of `Preadditive.LeftExact` in the scratch copy and removed it.
   Its two direct users import this module privately, so neither receives public
   reexports through it. All required signature names are already public through
   the retained import.
5. Compared the delivered node with its repository version. Only `proof`,
   `proof_deps`, and `proof_origin` change. Its two steps describe exactly the
   additive constructor and limit-preservation composition in Lean; the union
   of their uses equals `proof_deps`. The cited Mathlib source lines were read
   directly and agree with `proof_origin`.

Second reading changed only the unused public import and this report; the
worker's proof and node updates pass unchanged. The theorem and functor signatures
and definition remain unchanged.

Change record: `coord/changes/GlobalSectionsLeftExactImports.md` (unused public import).
