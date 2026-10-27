## Worker report

The single module `Sheaf.AlgebraicGeometry.QuasiSectionNearbyOpen` states
`AlgebraicGeometry.Scheme.Hom.exists_integral_closed_quasiSection_nearby_open`.
Its sole proof is `sorry`; no definitions, additional theorems, new nodes, or dependency
repairs are introduced. The item JSON changes only in `lean`.

Source read: `literature/stacks-project/more-morphisms.tex`, the full local-ring lemma
and proof 05GT and scheme lemma and proof 05GU, especially the final construction
`Z = closure {z}` with the reduced induced scheme structure. The integral and generic-point
formulation is already in the node and follows this explicit construction. There is no
statement correction or disputed assertion.

Every hypothesis and conclusion is represented as follows:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and S, morphism f | `{X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)` |
| f locally of finite type | `[LocallyOfFiniteType f]` |
| S locally Noetherian | `[IsLocallyNoetherian S]` |
| x in X; s defined as f(x) | `(x : X)`; each occurrence of s is the term `f x` |
| x closed in its scheme-theoretic fibre | `hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))` |
| Open subscheme V of X | `(V : X.Opens)`, with its canonical open-subscheme structure |
| A point x' in V | `hnearby : ∃ x' : X, x' ∈ V ∧ ...` |
| x belongs to the closure of x' | The next conjunct `x ∈ closure ({x'} : Set X)` |
| f(x') differs from s | The last conjunct `f x' ≠ f x` |
| Integral closed subscheme i : Z → X | `∃ (Z : Scheme.{u}) (i : Z ⟶ X), IsIntegral Z ∧ IsClosedImmersion i ∧ ...` |
| Generic point z of Z | `∃ z a : Z, IsGenericPoint z (Set.univ : Set Z) ∧ ...` |
| x belongs to i(Z) | `i a = x`, exhibiting its preimage a; a is unique since i is a closed immersion |
| Image of the generic point belongs to V | `i z ∈ V` |
| f(i(z)) differs from s | `f (i z) ≠ f x` |
| f composed with i quasi-finite at the point above x | `(i ≫ f).IsQuasiFiniteAtPoint a` |
| Closure of i(z) equals i(Z) | `closure ({i z} : Set X) = Set.range i` |
| Thus i(z) specializes to x | Follows from the explicit closure equality and `i a = x`, exactly as the node's final explanatory sentence |

No quasi-compactness, separatedness, global finite-type assumption, or closedness of x
in the whole of X is assumed. In particular, this concludes quasi-finiteness at a single
point, not on all of Z. The existential a simply supplies the point needed to type that
conclusion, and does not add mathematical data beyond membership of x in the closed subscheme.

Recorded statement dependencies used, with source signatures and docstrings inspected:

| Node | Module | Declaration used |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme and Scheme.Hom |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType | AlgebraicGeometry.LocallyOfFiniteType |
| pqf-def-locnoeth | Mathlib.AlgebraicGeometry.Noetherian | AlgebraicGeometry.IsLocallyNoetherian |
| def-pc-scheme-fibre | Mathlib.AlgebraicGeometry.Fiber | Scheme.Hom.fiber, asFiber, fiberHomeo |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | Canonical open subscheme associated to Scheme.Opens; IsOpenImmersion |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | AlgebraicGeometry.IsClosedImmersion |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint |
| pqf-def-quasifinite | WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism | AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint |

`IsGenericPoint z Set.univ` is literally `closure {z} = Set.univ`, as required.
`asFiber x` is the inverse image of x under `fiberHomeo`, so closedness is taken in the
actual scheme-theoretic fibre, not the ambient scheme. The project quasi-finiteness
predicate includes the finite-type requirement omitted by Mathlib's `QuasiFiniteAt`.
All universes and variables are explicitly bound; the common arbitrary universe u is
the universe of the schemes and their closed subschemes.

The already stated proof dependencies are imported without `public`, unless also a
statement dependency. Their modules are:

- `Mathlib.AlgebraicGeometry.Noetherian`: `LocallyOfFiniteType.isLocallyNoetherian`.
- `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`:
  `Scheme.fromSpecStalk_affine_description` and `Scheme.fromSpecStalk_local_properties`.
- `Mathlib.RingTheory.Localization.Submodule`: `IsLocalization.isNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Stalk`: `Scheme.SpecToEquivOfLocalRing`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic` and `Mathlib.RingTheory.Localization.Ideal`:
  `IsLocalization.AtPrime.orderIsoOfPrime` and `IsLocalization.orderIsoOfPrime`.
- `Sheaf.RingTheory.PuncturedLocalClosedPoints`:
  `PrimeSpectrum.exists_isClosed_singleton_of_isLocallyClosed_punctured`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `locallyOfFiniteType_iff`.
- `Sheaf.AlgebraicGeometry.ClosedFibrePointQuasiFiniteCriterion`:
  `Scheme.Hom.isQuasiFiniteAtPoint_of_closed_fibre_no_other_generalization`.
- The integral-scheme, closed-immersion and fibre proof dependencies are also statement
  dependencies and already have public imports.

The declaration docstring gives every one of the node's six proof steps and names the
DAG inputs: Noetherian local spectrum; the open in its puncture; choice of a closed point
there; reduced irreducible closure; the two possible generalizations and closed fibre;
then the affine finite-type quotient argument and closed-fibre criterion.

Edge cases checked mathematically before writing:

- X empty or V empty: the point/existence hypothesis cannot hold; no nonempty restriction
  has been introduced on the input schemes or open set.
- S a one-point scheme or f constant: the required unequal images cannot occur, so the
  implication is vacuous, exactly as the source.
- x may lie in V: this is permitted and does not identify x' with x; unequal images force
  x' to differ from x. V may also be all of X.
- Identity on the spectrum of a DVR, x its closed point, V its generic open: take Z to be
  the whole integral trait, z its generic point, a its closed point, i the identity.
- Nonclosed x in the total space: for the identity on Spec k[t], choose x = (0) and V the
  whole space; the closed-point condition is in the one-point fibre and the nearby
  hypothesis fails because x has no distinct generalization. The Lean does not replace
  fibre-closedness by ambient closedness.
- Nilpotents or reducible X are allowed. Integrality is required only of the selected Z,
  which is the reduced closure of the selected generic point in the source argument.
- No characteristic, residue-field, dimension, or cardinality restriction is introduced.

Searches for an existing statement (all via the prescribed tools):

- `grep` query: quasi.?section|nearby.?open|integral.*closed.*subscheme (subdirectory AlgebraicGeometry). Result: 0 hits; no matches. None constructs the prescribed integral closed quasi-section.
- `loogle` query: AlgebraicGeometry.LocallyQuasiFinite, AlgebraicGeometry.LocallyOfFiniteType. Result: 9 hits; AlgebraicGeometry.instLocallyQuasiFiniteOfLocallyOfFiniteTypeOfUniversallyInjective, AlgebraicGeometry.LocallyQuasiFinite.of_injective, AlgebraicGeometry.LocallyQuasiFinite.of_finite_preimage_singleton, AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton. None constructs the prescribed integral closed quasi-section.
- `leanfinder` query: For a locally finite type morphism to a locally Noetherian scheme find an integral closed quasi section through a closed fibre point whose generic point lies in a prescribed nearby open. Result: 8 hits; AlgebraicGeometry.IsLocallyNoetherian, AlgebraicGeometry.IsIntegral, AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace, AlgebraicGeometry.instIsGermInjectiveOfIsLocallyNoetherian. None constructs the prescribed integral closed quasi-section.
- `leansearch` query: A closed fibre point of a locally finite type morphism to a locally Noetherian scheme lies on an integral closed subscheme quasi finite at that point and meeting a prescribed open generalization. Result: 8 hits; AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints, AlgebraicGeometry.LocallyQuasiFinite.mk, AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian, AlgebraicGeometry.Scheme.Hom.fiber. None constructs the prescribed integral closed quasi-section.

Direct `rg -n` searches of `lean/WeilConjectures`, `lean/Sheaf`, and
`dag/lean_names_upstream.json` for `quasi.?[Ss]ection|nearby.?[Oo]pen` and for the exact
proposed declaration name found no matches. Searching the upstream tree for the item's
blueprint id also found no match. Existing local-finiteness, normalization and integrality
results do not provide this existence statement. No notion needs a private replacement.

Validation: the prescribed `scompile.py NP lem-sfb-quasi-section-nearby-open` completed
both the sandbox check and the library-module check with exit 0 and no errors or warnings.
No local build or direct Git command was run.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
