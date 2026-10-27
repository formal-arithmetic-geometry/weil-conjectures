## Worker report

Stage 2 states `AlgebraicGeometry.isIso_of_integral_birational_normal` in
`Sheaf.AlgebraicGeometry.IntegralBirationalNormalIsomorphism`. Its only proof is
`sorry`. The node copy changes only `lean`; no new nodes, dependency repairs or
statement corrections are needed.

The inherited BLOCKED ending referred to a completed stage-1 split, merged from
Q155 on 2026-10-23 at 10:40 UTC. The current node has no Lean record and
coord/queue.tsv lists it at stage 2. The stage-handoff paragraph of
coord/brief-stage2.md explicitly permits this stage-2 delivery without reopening
that split. The accepted statement and four proof steps are preserved.

Source read: literature/stacks-project/morphisms.tex, lemma-finite-birational-over-normal
(Tag 0AB1), lines 14630-14646. It explicitly says “finite (or even integral)” and
its affine argument does not assume Noetherianity or finite presentation.

Clause-by-clause correspondence:

- “Z and T integral schemes”: `{Z T : Scheme.{u}} [IsIntegral Z] [IsIntegral T]`.
  The universe `u` is explicit and arbitrary. Both are schemes in the same
  ambient category; there is no size restriction on test schemes or rings.
- Their generic points are Mathlib `genericPoint Z` and `genericPoint T`.
  Schemes are sober and these points are unique for integral schemes, so using
  the canonical generic points excludes no choice allowed by the node.
- “p : Z → T integral”: `(p : Z ⟶ T) [IsIntegralHom p]`. The class extends
  `IsAffineHom p` and requires `(p.app U).hom.IsIntegral` for every affine open
  `U`, exactly the node's affine-preimage and monic-equation conditions.
- “p(η_Z) = η_T”: `hgeneric : p (genericPoint Z) = genericPoint T`.
- “the induced homomorphism k(T) → k(Z) is an isomorphism”:
  `hbirational : Function.Bijective ((T.presheaf.stalkCongr
  (Inseparable.of_eq hgeneric)).inv ≫ p.stalkMap (genericPoint Z) :
  T.functionField ⟶ Z.functionField)`.
  Mathlib's `functionField` is definitionally the generic stalk. The stalk map
  has source the stalk at `p (genericPoint Z)`; the inverse stalkCongr transports
  from the stalk at `genericPoint T` to that source. This is the canonical induced
  map, not an arbitrary field isomorphism. Bijectivity of a commutative-ring
  homomorphism is equivalent to it being a ring isomorphism (and here a field
  isomorphism). No extra map is chosen.
- “every local ring of T is an integrally closed domain”:
  `hnormal : ∀ t : T, IsDomain (T.presheaf.stalk t) ∧
  IsIntegrallyClosed (T.presheaf.stalk t)`. This uses the dependency's prescribed
  inline normal-domain conjunction. The domain conjunct is explicit even though
  integrality of T already implies it.
- “p is an isomorphism of schemes”: `IsIso p`, in the category of schemes.
- “not assumed finite; no Noetherian or finite-presentation hypothesis”:
  the signature contains only the displayed hypotheses; it has no `IsFinite`,
  `IsLocallyNoetherian`, finite-type, or finite-presentation binder.

Dependency declarations read and used:

- def-pc-integral-scheme: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties, imported through the recorded function-field module.
  The class includes nonemptiness and domain sections on every nonempty open.
- def-sc-generic-point: `IsGenericPoint`, `genericPoint`, `genericPoint_spec`,
  Mathlib.Topology.Sober, imported transitively. Canonical generic points satisfy
  the recorded generic-point predicate.
- def-weil-finite-integral-morphism: `AlgebraicGeometry.IsIntegralHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Integral, public import. The node's record
  explicitly lists this integral companion of its main `IsFinite` declaration.
- def-sc-function-field: WeilConjectures.AlgebraicGeometry.FunctionField,
  public import of the recorded module. Its docstring directs the arbitrary
  integral-scheme clause to Mathlib `Scheme.functionField`; its component-product
  `Scheme.functionFieldOfComponents` is for the other clause and is not copied.
- def-weil-pbc-normal-ring: `IsDomain` and `IsIntegrallyClosed`,
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed, public import; the dependency
  explicitly prescribes the conjunction used here.

Proof dependencies are also imported for stage 3:

- `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen`,
  Mathlib.AlgebraicGeometry.FunctionField (through the public upstream import).
- `IsAffineOpen.isLocalization_stalk`, `fromSpec_app_self`,
  `fromSpec_primeIdealOf`, `isOpenImmersion_fromSpec` (AffineScheme),
  `Scheme.Hom.germ_stalkMap` (Scheme), and the open-immersion stalk-map isomorphism
  instance (OpenImmersion): all available through the scheme imports. These give
  the clauses of lem-weil-pbc-affine-open-stalk-localization.
- `IsIntegrallyClosed.of_localization_maximal`,
  Mathlib.RingTheory.LocalProperties.IntegrallyClosed, ordinary proof import.
- The affine property of `MorphismProperty.isomorphisms Scheme`, instance
  `AlgebraicGeometry.instHasAffinePropertyIsomorphismsSchemeAndIsAffineIsIsoCommRingCatAppTop`,
  Mathlib.AlgebraicGeometry.Morphisms.IsIso, ordinary proof import.
- `AlgebraicGeometry.Scheme.Cover.glueMorphisms`, `ι_glueMorphisms`, and `hom_ext`,
  Mathlib.AlgebraicGeometry.Gluing, ordinary proof import.

Edge cases checked before writing:

- Empty Z or T are excluded by the node's integral-scheme hypothesis itself;
  empty affine opens inside T cause no problem, since the proof uses nonempty
  affine opens covering the nonempty target.
- The identity of any integral scheme with normal local rings satisfies all
  hypotheses, in any characteristic and without Noetherianity.
- For Spec L → Spec k with L/k a nontrivial algebraic extension, integrality
  alone holds but the canonical generic field map is not surjective; hbirational
  correctly excludes this non-isomorphism.
- Cusp normalization is integral and birational but its target has a nonnormal
  local ring, so hnormal excludes it.
- Spec Z[1/2] → Spec Z is birational with normal target but is not integral;
  IsIntegralHom correctly excludes this non-isomorphism.
- A normal non-Noetherian domain and its identity are allowed. No finite or
  finite-presentation restriction is hidden in IsIntegralHom.
- The transported map has the correct contravariant direction from k(T) to k(Z).
  No separate dominance hypothesis is necessary: hgeneric expresses the node's
  generic-point condition, and the section-map injectivity follows as in its proof.

Searches made on 2026-10-23:

- msearch.py leanfinder, query “An integral birational morphism of integral schemes
  to a scheme with integrally closed local rings is an isomorphism”: 8 hits,
  chiefly `Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom` and normalization
  construction instances. Read Mathlib/AlgebraicGeometry/Normalization.lean:270-308;
  the hit concludes IsIso f.toNormalization, not IsIso f. No exact match.
- msearch.py loogle, query `"IsIntegralHom", "IsIso"`: one hit, that same
  relative-normalization instance; no exact match.
- msearch.py grep, query `birational|IsIntegralHom.*IsIso|isIso.*birational` in
  AlgebraicGeometry: 9 hits, principally normalization and birational module
  headers; no exact normal-target integral-morphism theorem.
- msearch.py leansearch, query “An integral birational morphism of integral schemes
  with normal target is an isomorphism”: 8 hits, normalization, integral-morphism
  definitions and stability, and finite iff integral plus locally finite type;
  no exact statement.
- rg in lean/WeilConjectures and lean/Sheaf for integral/birational/normal and
  isIso combinations: found `isIso_of_finite_birational_normal` in
  Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso; read its full signature and
  docstring. It assumes IsFinite, so it does not state this integral variant.
  Proper-birational curve results also have additional restrictions. The upstream
  NormalizationDenseOpen result assumes local Noetherianity and concerns a
  different arrow. No exact match.
- grep -rn for the exact item id in lean/WeilConjectures: no hit.
- rg for the proposed declaration name in Mathlib, lean/WeilConjectures,
  lean/Sheaf, and dag/lean_names_upstream.json: no existing declaration.

Validation: scompile.py compiled this delivered file separately as both sandbox
and library module against the live published build, cleanly (1.9 and 3.3 seconds).
All binders/universes are explicit; autoImplicit is disabled. No definitions or
helper theorems were introduced. No statement dispute or node fault found.

## Second reading by Q120

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
