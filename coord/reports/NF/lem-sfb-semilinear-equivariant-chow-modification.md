## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearEquivariantChowModification` states
`AlgebraicGeometry.exists_semilinear_equivariant_chow_modification`, with its sole proof
`sorry`. There are no new definitions, helper theorems, new nodes, dependency repairs,
or changes to the informal statement. All nine proof steps are in the theorem docstring.

Hypothesis and conclusion correspondence:

- Field k: `(k : Type u) [Field k]`.
- Integral finite-type k-scheme X: `(X : Scheme.{u}) [IsIntegral X]` and the specified
  structure map `f : X ⟶ Spec (.of k)`. `[IsProper f]` includes
  `LocallyOfFiniteType f`; its `UniversallyClosed` parent implies `QuasiCompact f`.
  Thus it includes exactly the finite-type and proper hypotheses, without redundant
  overlapping instance binders.
- Finite group: `(H : Type v) [Group H] [Finite H]`. Its universe is independent of u;
  there is no bound on the universe in which the finite group is presented.
- Action on k: `rho : H →* (k ≃+* k)`, using Mathlib's ring automorphisms and their
  composition multiplication. Action on X: `a : H →* Aut X`, using the existing
  categorical automorphism group. Both are arbitrary homomorphisms; neither is assumed
  injective or faithful.
- Compatibility: `ha` states `(a h).hom ≫ f = f ≫ Spec.map (ofHom (rho h⁻¹).toRingHom)`.
  The inverse is essential: contravariance of Spec converts the left field action
  into the left scheme action on the field spectrum. This is also the convention
  in the landed CommonFieldSemilinearInduction module.
- Integral finite-type T: existential `(T : Scheme.{u}) (_ : IsIntegral T)` and
  `LocallyOfFiniteType (q ≫ f) ∧ QuasiCompact (q ≫ f)`. Its specified structure map
  is `q ≫ f`, which expresses that q is a morphism of k-schemes without redundant
  existential choices of an equal structure morphism.
- Compatible action on T: existential `aT : H →* Aut T` and the first universal
  equation, with the same inverse field action as ha.
- Equivariance: `(aT h).hom ≫ q = q ≫ (a h).hom` for every h.
- Properness and surjectivity: `IsProper q ∧ Surjective q`.
- Isomorphism over a dense open: `∃ U : X.Opens, Dense (U : Set X) ∧ IsIso (q ∣_ U)`.
  Mathlib's morphism restriction is the map from the inverse-image open to U, so
  this asserts an isomorphism over U, not merely that q has a section there.
- Both finite projective-space embeddings: `IsHProjective (q ≫ f) ∧ IsHProjective q`.
  This is the recorded def-kun-projective declaration, whose witness is a finite
  coordinate type and a closed immersion factoring the morphism. For integral
  (hence nonempty) T the coordinate type is nonempty and can be enumerated as
  Fin (N+1). It is exactly the node's finite-dimensional embedding convention.
- The identification k(T) = k(X) induced by q: the last existential supplies
  `eta : T`, `IsGenericPoint eta Set.univ`, `q eta = genericPoint X`, and
  `IsIso (q.stalkMap eta)`. The definition of `Scheme.functionField` is the generic
  stalk, and generic points of schemes are unique. Hence this is exactly the
  canonical map from k(X) to k(T), up to the canonical transport along those point
  equalities. IsIso is a ring isomorphism, thus an isomorphism of these fields.
  It is stronger information than an unspecified abstract isomorphism and precisely
  expresses the node's assertion that q itself induces the identification.

Dependency declarations used (full signatures and docstrings read):

- def-weil-field: Mathlib.Algebra.Field.Defs, `Field`.
- def-pc-integral-scheme: Mathlib.AlgebraicGeometry.Properties, `IsIntegral`.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  `LocallyOfFiniteType`, and Morphisms.QuasiCompact, `QuasiCompact`.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Proper, `IsProper`,
  extending `IsSeparated`, `UniversallyClosed`, and `LocallyOfFiniteType`.
- def-weil-surjective-morphism: Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap,
  `Surjective` (surjectivity on underlying points).
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion, `IsOpenImmersion`;
  here `X.Opens` and `q ∣_ U` use Mathlib's canonical open subschemes.
- def-kun-projective: WeilConjectures.AlgebraicGeometry.Morphisms.Projective,
  `AlgebraicGeometry.IsHProjective`.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  `IsClosedImmersion`, used by the canonical `IsHProjective` definition.
- def-sc-function-field: WeilConjectures.AlgebraicGeometry.FunctionField, the recorded
  `Scheme.functionFieldOfComponents` module and its explicit instruction to use
  Mathlib's `Scheme.functionField` for integral schemes. The latter is exactly
  `X.presheaf.stalk (genericPoint X)`. We use those actual stalks and q's stalk map.

All recorded stated proof-dependency modules are imported, plain rather than public.
These include NoetherianChowModification, ClosedImmersionProducts,
ProjectiveSpace.Product, ReducedSchemeImage, ProjectiveImpliesProper, and the
upstream SchemeTheoreticallyDominant module. The existing Mathlib proof leaves are
covered by their defining Noetherian, Limits, ClosedImmersion, Separated, IdealSheaf,
and FunctionField modules. No upstream or library file was edited.

Edge cases checked before writing:

- The trivial group allows the ordinary projective Chow modification; the action
  existential does not force nontriviality or faithfulness.
- Nonfaithful field or scheme actions, including completely trivial actions, satisfy
  the binders. No free-action, tameness, normality, smoothness, or geometric-integrality
  hypothesis occurs.
- Arbitrary characteristic, including characteristic dividing the group order:
  no division by the group order is present.
- Nontrivial actions on k are preserved by the inverse-Spec convention; the scheme
  automorphisms are not required to be k-linear.
- X = Spec k and other zero-dimensional proper integral schemes are included.
- The empty scheme is excluded by integrality, as in the node; dense opens therefore
  cannot be empty. A group cannot be empty, so finite averaging has a nonempty index.
- IsHProjective permits a finite coordinate type; integrality prevents an empty
  projective ambient space from being a spurious witness.

Searches actually run:

- msearch.py leanfinder: "Finite semilinear group action on a proper integral scheme
  admits an equivariant projective birational modification". Eight hits, on ordinary
  Proj properness, finite global sections and linear projectivization. None states
  the equivariant Chow result.
- msearch.py loogle: "AlgebraicGeometry.IsHProjective,
  CategoryTheory.Aut, AlgebraicGeometry.Scheme.Hom.stalkMap". Zero hits; service says
  IsHProjective is unknown (it is a project declaration, not Mathlib).
- msearch.py grep: "Chow|equivariant.*projective|projective.*birational" in
  Mathlib/AlgebraicGeometry. Zero hits.
- rg of WeilConjectures and Sheaf for the node id, theorem name and equivariant-Chow
  patterns: the flat-curve preparation and curve-pencil docstrings cite the intended
  construction, but there is no declaration stating this node. The same search of
  dag/lean_names_upstream.json produced no match.
- rg of the project and Mathlib for actions, Aut, functionField, generic stalk maps,
  IsHProjective and dense-open modification signatures: reused the existing Aut and
  RingEquiv types and Scheme.Hom.stalkMap directly. No notion is privately copied.

Source inspection: Stacks coherent.tex, lemma-chow-Noetherian (Tag 0200), states
proper surjective Chow modification, projective-space immersion, and a dense
isomorphism open. Properness over the field makes the immersion closed. The Segre
lemma in constructions.tex (Tag 01WD) gives the finite product embedding. The
node's nine-step semilinear averaging and closure proof is retained in the docstring.
No STATEMENT-DISPUTED issue or informal node fault was found.

Validation: initial scompile.py compile succeeded with only a redundant-instance
warning; removed the redundant finite-type input instance binders and retained their
mathematical content through IsProper f. Final scompile.py run compiled both the sandbox probe and the library module cleanly
(1.9 s and 2.0 s, no warnings). The prescribed deliver2.py --no-push run printed
OK: preflight and compilation passed. All delivered theorems remain sorry-only.

## Second reading by NF

The dispatcher brief assigns the independent review to the maintainer after delivery
and forbids starting other agents. No independent second reading is claimed here.
The worker re-read the node and complete file against the clause correspondence above.
That self-check verifies the inverse field action, both H-projectivity clauses, the
actual isomorphism over U, and the actual stalk map rather than an arbitrary field
isomorphism. The only compilation adjustment was removal of redundant finite-type
instance binders already implied by properness.
