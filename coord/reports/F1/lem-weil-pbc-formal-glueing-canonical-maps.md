## Worker report

The module `Sheaf.Paper.FormalGlueingCanonicalMaps` states all three clauses in four
named theorems, all with proof `sorry`. No definitions are introduced. The item keeps
its statement and gains `def-weil-pbc-formal-glueing-data` in `stmt_deps` because the
landed module for that node already defines precisely the canonical actions and maps
needed here. Using them avoids a second definition of any notion.

Hypotheses and objects:

- Commutative rings are `[CommRing R]`, `[CommRing S]`; the ring map is the arbitrary
  binder `φ : R →+* S`. `restrict φ` restricts scalar multiplication along this very
  map, and `extend φ` uses `φ.toAlgebra`, so there is no unrelated algebra structure.
- Arbitrary R-modules are `P : ModuleCat R`, and the maps in clause (1) are arbitrary
  R-linear maps between additive commutative groups with `Module R` structures.
  S-modules in the second part of (1) are arbitrary `Q Q' : ModuleCat S`, restricted
  with `restrict φ`. This bundling neither adds nor drops module hypotheses.
- The elements are arbitrary `e`, `f`, `g : R`, with no nonzero or regularity condition.
  Separate explicit universes cover R, S, P, and the three modules used in (1).

Clause-by-clause rendering:

1. `LocalizedModule.away_map_functorial` sets T to `Submonoid.powers e`, and lQ,
   lQ', lQ'' to the recorded `LocalizedModule.mkLinearMap`. Its three conjuncts state
   exactly localization of composition = composition of localizations, localization
   of a sum = sum of localizations, and localization of the identity = identity.
   Localization of a map is the recorded Mathlib operation `IsLocalizedModule.map`.
   `FormalGlueing.localizedSModule_properties` uses the existing actual module
   structure `localizedSModule φ e Q`; it is a `Module S`, so its module laws are
   supplied, rather than hidden in a hollow hypothesis. The first conjunct states
   s(q/e^n) = (sq)/e^n for every s, q and n. The second, `m.smul (φ r) x = r • x`,
   says that restriction to R is the original R-module structure. The third is
   S-linearity of q ↦ q/1 (additivity is already provided by mkLinearMap).
   The fourth says precisely that `localMap e (restrictMap φ h)` commutes with
   the two chosen S-actions whenever h is S-linear (R-linearity and additivity
   are already in its linear-map type). This includes every assertion of (1).
2. `FormalGlueing.swap_properties` has bijectivity of f and of g on
   `localize f (localize g P)` as its first two conjuncts. The third is exactly
   `(p/f^a)/g^b ↦ (p/g^b)/f^a` for the already defined `swap f g P`.
   Setting a=b=0 gives the prescribed generator values. The fourth says that
   any R-linear t has those generator values iff t is that swap, expressing
   existence and uniqueness, not merely existence of some isomorphism.
   The last two conjuncts state that `swap g f P` is its inverse on both sides;
   these R-linear maps therefore are R-module isomorphisms. The theorem can
   equally be instantiated with f and g reversed to get the reverse fraction formula.
3. `FormalGlueing.compare_properties` uses `letI : Algebra R S := φ.toAlgebra`.
   Its first conjunct is bijectivity of f on `restrict φ (extend φ (localize f P))`.
   The second states `(s ⊗ p)/f^n ↦ s ⊗ (p/f^n)`; n=0 gives the stated values
   on pure tensors localized with denominator 1. The third is uniqueness among
   ALL R-linear maps with those n=0 values, and also states that the existing
   comparison has those values (the equivalence is bidirectional). The fourth
   is S-linearity for `localizedSModule` of (1). The last is bijectivity of the
   same comparison. Together with its additive and R-linear map type, these
   express exactly an S-module isomorphism. The tensor products are in the
   order `S ⊗[R] P` used by the dependency's recorded `LinearMap.baseChange`;
   this is the node's `P ⊗[R] S` under `TensorProduct.comm`, with the S-action
   now on the first factor. No alternative tensor product or scalar action is defined.

Dependency declarations read and used:

- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`,
  `LocalizedModule.Away`, `LocalizedModule.mk`, `LocalizedModule.mkLinearMap`,
  `IsLocalizedModule.map`; their signatures, docstrings and fraction semantics were
  read. These are the two recorded module-localization dependencies.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `LinearMap.baseChange`;
  signature and docstring read. It is used by `FormalGlueing.extendMap` in the
  imported dependency; `extend` is `S ⊗[R] P` with `TensorProduct.leftModule`.
- `Sheaf.RingTheory.FormalGlueingData`: `FormalGlueing.restrict`, `localize`,
  `extend`, `localizedSModule`, `localMap`, `restrictMap`, `swap`, `compare`;
  all declarations and their supplying named existence theorems were read in full.
  Their fraction and generator specifications coincide with this item's objects.
  In particular the chosen actions and maps here are the very ones already used
  in formal glueing data, rather than new copies.

Edge cases checked mathematically before the final signatures: R or S the zero ring,
P=0, Q=0, f=0, g=0, nilpotent f or g, f=g, f=1, g=1, and exponents zero.
Powers containing zero yield the zero localization; all inverse and uniqueness
statements remain valid. No injectivity of P → P_f, flatness of S, or integrality
hypothesis has been added. There is no finite index set or characteristic restriction.

Searches:

- `msearch.py ... leansearch "module localization commutes with another localization
  and base change"`: unavailable (Internal Server Error); recorded as unavailable,
  with no verdict inferred from that failure.
- `msearch.py ... leanfinder "localizing a module at two elements commutes and
  localization commutes with extension of scalars"`: eight hits, including
  `IsLocalizedModule.of_restrictScalars`, `IsLocalization.localization_localization_isLocalization`
  and scalar-extension equivalences. None states this item's full three clauses.
- `msearch.py ... loogle "IsLocalizedModule.map, IsLocalizedModule.module"`:
  zero hits for that query.
- `msearch.py ... grep "map_comp|def module|Away.*commut" Algebra/Module/LocalizedModule`:
  five hits including `map_comp`, `map_comp'` and `IsLocalizedModule.module`.
  These cover components, not the whole statement; the latter module construction
  concerns an algebra which is a localization, not an arbitrary S as here.
- `rg` on Mathlib, upstream `WeilConjectures`, `dag/lean_names_upstream.json`
  and project `lean/Sheaf` for the four proposed declaration names and the item id:
  no name collisions; no upstream statement for this item. Project hits for the
  item id identified `FormalGlueingData`'s named existence and S-linearity theorems.
  Those supply some subclauses but do not assert functoriality, the swap inverse,
  invertibility on the comparison target, or comparison bijectivity together.
  The final file reuses their definitions and adds the remaining complete properties.
- Broader `rg` for `LocalizedModule|baseChange|canonical.*maps` in project/upstream
  sources found unrelated localized-module and base-change statements; no exact match.

Sources checked directly at [05EL](https://stacks.math.columbia.edu/tag/05EL),
[07K0](https://stacks.math.columbia.edu/tag/07K0), and
[00DK](https://stacks.math.columbia.edu/tag/00DK), since the local literature checkout
on this machine does not contain the TeX files. These give respectively the canonical
maps, localization universality, and localization/tensor compatibility.
No statement correction, new definition node, unusable dependency, or disputed
statement was found. The node's seven proof steps are distributed among the four
statement docstrings. No mathematical theorem is proved in this delivery.

Validation: the final module compiled on the server in 2 seconds, with no errors
or warnings. All variables and universes are explicitly bound.

## Second reading by F1

I independently opened the node statement and the complete Lean module and matched each
object, hypothesis, and conclusion clause.

- Rings and map: the node's commutative rings `R`, `S` and homomorphism `φ` render as
  `{R : Type u} {S : Type w} [CommRing R] [CommRing S] (φ : R →+* S)` in all relevant
  declarations. No injectivity, finiteness, characteristic, or universe restriction is
  added.
- Modules and localization: the node's arbitrary `R`-module `P`, elements `f,g,e`,
  localization and localization of maps render as `ModuleCat`, `localize`,
  `LocalizedModule.mk`, and `localMap`; `away_map_functorial` uses arbitrary linear maps
  and states composition, addition, and identity exactly as clause (1).
- Localized S-action: `localizedSModule_properties` uses the existing action from
  `FormalGlueingData`, and its four conjuncts give the fraction action formula, the
  restricted R-action, S-linearity of the localization map, and S-linearity of localized
  S-linear maps. The displayed fraction equalities are equivalent to the node's map
  assertions and do not add hypotheses.
- Iterated localization: `swap_properties` states bijectivity of multiplication by both
  `f` and `g` on `(P_g)_f`, the generator and fraction formula for the unique swap map,
  and both inverse composite identities. This matches clause (2), including zero and
  nilpotent denominators.
- Base change: `compare_properties` introduces `Algebra R S := φ.toAlgebra`, uses the
  dependency's extension-of-scalars object `S ⊗[R] P` (the recorded Mathlib
  `LinearMap.baseChange` representation of the node's `P ⊗[R] S`), and states f's
  bijective action, the pure-tensor fraction formula, uniqueness on pure tensors,
  S-linearity, and bijectivity. Quantifier order and domains/codomains agree with clause
  (3), and no extra flatness or injectivity is assumed.

Edge cases checked: zero rings and zero modules, empty/zero localizations, `f = 0`,
`g = 0`, nilpotent or equal denominators, `f = 1`/`g = 1`, and exponent `0`; all are
covered by the unrestricted ring/module binders and powers construction. There is no
index-set or characteristic hypothesis in this node.

I searched Mathlib and the slopmaster2 source/project with `rg`, and ran the recorded
LeanSearch/LeanFinder/Loogle/grep searches in `searches.jsonl`. They found only component
lemmas (`IsLocalizedModule.map`, `LinearMap.baseChange`, and related localization facts),
not the complete three-clause statement; the existing FormalGlueingData declarations are
used directly. No duplicate definition, missing dependency, or statement correction was
found, so no source or node change was needed.

The module compiles cleanly with `scompile.py`; all four theorem proofs remain `sorry` as
required for stage 2, and every declaration/docstring carries the source and blueprint.
