## Worker report

Item: `lem-sfb-finite-branch-ample-descent`. The module
`Sheaf.AlgebraicGeometry.FiniteBranchAmpleDescent` states
`AlgebraicGeometry.Scheme.Modules.exists_ample_descent_of_finite_branches`.
It has one theorem, whose entire proof is `sorry`, and no new definitions.
The node changes only in `lean`. There is no statement correction or disputed claim.

Hypotheses, matched individually:

- The commutative Noetherian ring is `(R : Type u) [CommRing R] [IsNoetherianRing R]`.
- `S = Spec R` is written explicitly as `Spec (CommRingCat.of R)` throughout.
- The schemes `X,Y` carry `Over S` instances; their structure morphisms have
  `IsProper` instances. These are precisely proper schemes over this affine base.
- The morphism `a : X ⟶ Y` has `a.IsOver S`, `IsFinite a`, and `Surjective a`.
- The closed subscheme is `(T : Scheme.{u}) (t : T ⟶ Y) [IsClosedImmersion t]`.
- `Z` is the actual chosen fibre product
  `CategoryTheory.Limits.pullback (C := Scheme.{u}) a t`; `Finite` applies to its
  underlying point type. No assumption about rational points or residue fields is made.
- `D : Y.Opens` and `hD : (D : Set Y) = (Set.range t)ᶜ` name exactly the complement
  of the closed subscheme. This is a presentation of an existing canonical open,
  not an additional geometric hypothesis: a closed immersion has closed range.
  The inverse-image open `a ⁻¹ᵁ D` is the complement of the image of `Z` in `X`,
  because the square defining `Z` is cartesian. The hypothesis
  `[IsIso (a ∣_ D)]` says that the morphism induced by `a` itself is an isomorphism
  between those complements; it does not supply an unrelated isomorphism.
- `(L : X.Modules) [L.IsInvertible] (hL : IsAmple X L)` uses the recorded notions
  of invertibility and absolute ampleness, with no tensor power replacing `L`.
- The specified affine open is `(U : X.Opens) (hU : IsAffineOpen U)`.
  `hZU` asserts that the range of the actual first projection from `Z` is in `U`.

Conclusion, matched individually:

- `∃ W : Y.Opens, Set.range t ⊆ (W : Set Y)` is the open neighbourhood of `T`.
- `Nonempty (L.restrict (a ⁻¹ᵁ W).ι ≅ SheafOfModules.unit _)` is the asserted
  trivialization of `L` over the inverse image of `W`.
- `∃ (M : Y.Modules) (hM : M.IsInvertible)` produces an invertible module on `Y`.
- `Nonempty (M.restrict W.ι ≅ SheafOfModules.unit _)` trivializes `M` on `W`.
- `Nonempty ((tensorPullback a).obj M ≅ L)` is precisely the module descent.
- The isomorphism from `M.restrict D.ι` to
  `(tensorPullback (inv (a ∣_ D))).obj (L.restrict (a ⁻¹ᵁ D).ι)` identifies `M` on
  the complement with the transport of `L` through the specified isomorphism.
  The inverse exists because the actual restricted morphism `a ∣_ D` is an iso.
- `@IsAmple Y M hM` asserts ampleness of the same descended module.
- `∃ (n : ℕ) (i : Y ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)), ...` gives the specified
  closed immersion with `i ≫` the structure projection equal to `Y ↘ S`.
  Naturals encode the integer `n ≥ 0`; `ULift` only puts the `n+1` coordinates in
  the scheme universe and does not change their number. The additional
  `IsHProjective (Y ↘ S)` is the node's explicit “in particular” clause.

Dependency declarations read and used (public statement imports):

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and `pullback.fst`, instantiated in `Scheme`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  opens and their inclusions use the standard scheme restriction API.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: the public upstream
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; the recorded normalized
  adjunction interface is imported, without recreating any pullback functor.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, using the canonical `ProjectiveSpace`.

Restriction is Mathlib `Scheme.Modules.restrict` from
`Mathlib.AlgebraicGeometry.Modules.Sheaf`, whose full source definition was read.
Its sheaf of rings is the one on the actual open subscheme. The structure module is
`SheafOfModules.unit`, as in the definition of invertibility. All global and
isomorphism-transport pullbacks use the dependency's tensor-formula pullback.

The stated proof dependencies are imported privately: scalar extension of Proj,
module-pullback identity/composition, ampleness invariance, nonvanishing on finite
sets, finite-surjective ampleness reflection, ample immersion over an affine base,
gluing modules, nonvanishing-section trivialization, tensor-pullback restriction,
and the Mathlib proper/closed-image/quasi-finite/separated/closed-immersion APIs.
The docstring gives all seven DAG proof steps, including closed-image shrinking,
the explicit two-open transition and inverse, pullback compatibility, and passage
to the finite-projective-space convention. No dependency module or helper is needed.

Sources checked: the source files in the node, particularly Properties 0F20
(`lemma-quasi-affine-invertible-nonvanishing-section`), Coherent 0B5V
(`lemma-surjective-finite-morphism-ample`), and the closed-image shrinking in
Divisors `lemma-finite-trivialize-invertible-upstairs`. The current blueprint is
`literature/blueprint/latest`; the item is an extracted tool, with null unit ancestor,
rather than the unit's own statement. The exact item id has no blueprint occurrence.

Edge cases checked before writing and again against the signature:

- Empty `Z`: surjectivity forces `T` empty. `D = ⊤` is permitted; `W = ⊥` is
  permitted. Transport through the isomorphism gives the required descent.
- Empty schemes and the zero base ring are allowed: no `Nonempty`, domain,
  integral, connected, normal, positive dimension, or nontrivial-ring binder occurs.
- Nonclosed points of `Z` are allowed: finiteness concerns all topological points,
  not closed points or residue-field rational points. Stacks 0F20 applies to any
  finite subset in the given affine open.
- The case `n = 0` gives one homogeneous coordinate and is not excluded.
- Neither `a` flat nor a group action nor an étale branch condition occurs.
- One arbitrary universe `u` is used for the base ring and schemes; the coordinates
  are lifted into it. There is no independent smaller test-object universe and
  there are no auto-bound variables, statement `let`s, or local notations.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query “An ample line bundle descends under a
  finite surjective morphism which is an isomorphism away from a finite closed
  subset”: eight hits, chiefly `IsFinite.finite_app`, affine covers, and morphism
  descent; none descends this line bundle through a possibly nonflat map.
- `msearch.py ... loogle` with query `"ample", "descent"`: zero hits.
- `msearch.py ... grep` with query `ample.*descen|descen.*ample|finite_branch` in
  `AlgebraicGeometry`: zero Mathlib hits.
- Direct `rg` for `ample.*descen|descen.*ample|FiniteBranchAmple|finite_branch_ample`
  in both `lean/WeilConjectures` and `lean/Sheaf`: related ampleness/fpqc/normal
  descent results only. `FiniteNormalAmpleDescent` requires a normal integral
  target and produces existence of a bundle, so does not state this lemma.
- `grep -rn 'lem-sfb-finite-branch-ample-descent' lean/WeilConjectures`: no hit.
- `rg` for the new declaration name in `dag/lean_names_upstream.json`, both
  project roots, and Mathlib: no collision.

Validation uses only `scompile.py` and `deliver2.py`. Compiler-guided repairs
qualified the categorical fibre product to avoid the module-pullback namespace
and fixed its ambient category explicitly to prevent expected-type inference
from choosing `Type`. These repairs change no mathematical hypothesis.

## Second reading by NX

This is the worker's fresh clause-by-clause self-check; the dispatch brief assigns
independent review to the maintainer, and prohibits starting another agent.
On rereading the node and full theorem, I checked in particular that the iso is
induced by `a`, that `Z` is the actual scheme fibre product, and that the last
identification transports along the inverse of that same iso. The chosen `L`,
not a tensor power, descends. Every output sheaf is on the actual scheme/open,
not a sheaf on a substitute site. Both properness hypotheses, the Noetherian
base, the specified affine neighbourhood and all three morphism properties are
present. The finite-space embedding uses `n+1` coordinates, its structural
commutativity is explicit, and its closed-immersion property is retained. No
mismatch, missing helper, or statement correction was found in this rereading.
