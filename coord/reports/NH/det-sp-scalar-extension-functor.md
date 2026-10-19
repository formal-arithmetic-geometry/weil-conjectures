## Worker report

Repair of the independently reviewed immutable head `a4717a1495b7` for
`det-sp-scalar-extension-functor`. The saved packet was inspected first and its
prescribed dry run passed as `5f6cecc290`. A clause-by-clause self-check nevertheless
confirmed all the mathematical omissions in the return, so this delivery repairs
them rather than repushing that packet. The sandbox node agrees with the current
shared node outside `lean`; no statement, proof, dependency, or unit field changes.
The module remains `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.

The real functor is still `AlgebraicGeometry.ProEtale.scalarExtensionFunctor :=
scalarExtension f T`. It uses the published ordinary, uncompleted derived
extension on sheaves of constant-ring modules. There is no new localization,
tensor product, constructibility predicate, or Tor predicate. New helpers are
normalizations and comparisons belonging to this node's four clauses. Every
postponed proof is a named theorem with this node's blueprint tag and its
natural-language proof steps; all definitions have actual data. The comparison
choices come from uniqueness statements, never a bare `Nonempty` isomorphism.

Hypotheses and clauses, matched individually:

* `T : Scheme.{u}` permits every scheme, with no Noetherian, separatedness, or
  characteristic assumption. `A B C : Type u`, their `CommRing` instances and
  `f : A →+* B`, `g : B →+* C` give the specified unital coefficient maps.
  The published functor and its comparisons are available even for general
  commutative rings; they specialize to the node's finite torsion rings.
  The preservation theorem binds `[Finite A] [Finite B]`, `ℓ : ℕ`,
  `[Fact ℓ.Prime]`, and the two hypotheses
  `∃ n : ℕ, ∀ x, (ℓ ^ n) • x = 0`, exactly power-of-ell annihilation.
* Ordinary derived categories are `Scheme.proEtaleDerivedCategory T A`, over
  `proEtaleConstantRing T A`, the constant sheaf of `ULift A` in the site's
  module universe. The ULift is the published size convention. The site retains
  object universe `u+1` and morphism universe `u`; no equality is imposed.
* Clause 1: `scalarExtensionFunctorCounit` is the published
  `reductionScalarComplexCounit`. `scalarExtensionFunctor_kflat_representation`
  asserts its invertibility on every K-flat `P`.
  `scalarExtensionFunctorKFlatIso` explicitly has endpoints
  `(scalarExtensionFunctor f T).obj (DerivedCategory.Q.obj P)` and
  `DerivedCategory.Q.obj ((reductionChangeComplex T (proEtaleConstantRingMap f)).obj P)`.
  Thus it computes this particular functor along this particular ring map,
  with the target-ring action of ordinary scalar extension. The K-flat predicate
  is the retained `CochainComplex.IsKFlat.{u+1,u}` on this actual site.
  `scalarExtensionFunctor_map` says its arrow action, under the same counit,
  is the localization of termwise scalar extension of the input chain map.
  The published ordinary functor's map is `id_B tensor u`, equivalently
  `u tensor id_B` in the paper's factor order.
  `scalarExtensionFunctor_exact` states commuting shifts and `IsTriangulated`.
* Clause 2: `hbounded` is finiteness of the set of degrees with nonzero
  cohomology; `hconstructible` requires the retained intrinsic
  `IsConstructibleProEtaleModuleSheaf T A` on each cohomology sheaf. Both are
  re-exported by the recorded constructibility module. `hTor` is the retained
  `HasProEtaleTorAmplitude T A K a b`, re-exported by the recorded coefficient
  Tor module; it includes `a ≤ b` and tests every degree-zero module sheaf.
  `scalarExtensionFunctor_preserves_constructible_tor` concludes boundedness,
  intrinsic constructibility of every cohomology sheaf, and
  `HasProEtaleTorAmplitude T B ((scalarExtensionFunctor f T).obj K) a b` with
  the identical `a,b`. Hence finite Tor amplitude is included in the output.
  There is no flatness or projective-dimension hypothesis on the coefficient map.
* Clause 3, arbitrary line: `hL : L.IsFiniteLocallyFreeOfRank 1` is local
  isomorphism to the coefficient unit. `scalarExtensionFunctor_line` states
  that its degree-zero counit is invertible and its ordinary scalar extension
  remains rank one. `scalarExtensionFunctorLineIso` explicitly identifies
  derived scalar extension of `L[0]` with the degree-zero ordinary tensor.
  `proEtaleRingExtension_obj` identifies the ordinary object with the existing
  sheafified `changeOfRings`; its B action is retained.
* Clause 3, Tate construction: `scalarExtensionTateLine` is only an abbreviation
  for `coefficientTwistLine` applied to the dependency's `tateFiniteLine`.
  Its input is precisely the roots module tensored along the unique quotient
  coefficient map. The index `n : ℕ` means the common exponent `m=n+1 ≥ 1`.
  `a : ZMod (ℓ ^ (n+1)) →+* A` is that unique quotient map; the B map is
  `f.comp a`, so both rings are killed by the same power. Conversely the
  annihilation hypothesis supplies this unique quotient map, as in the recorded
  Tate dependency. `coefficientTwistLine` uses positive tensor powers, the unit
  at zero, and the recorded internal Hom dual for negative integers.
* Clause 3, Tate comparison: the extra assumption is exactly
  `[∀ x : T, Invertible (ℓ : T.residueField x)]`.
  `ScalarExtensionTateMaps` and `IsCanonicalScalarExtensionTateMaps` specify
  the coefficient map at zero, the identity root map with scalar map f at one,
  tensoring in positive degrees and dual evaluation in negative degrees.
  `scalarExtensionTateMaps_existsUnique` determines this family uniquely.
  `scalarExtensionTateIso_existsUnique` uniquely specifies the isomorphism
  on each ordinary scalar tensor by `b tensor x ↦ b*c(x)`.
  `scalarExtensionFunctor_tate` states rank one of both signed lines and the
  invertible derived counit. `scalarExtensionFunctorTateIso` composes that
  counit with the standard single-complex comparison and this fixed ordinary
  isomorphism. It is the canonical `(A_T(r))_B ≅ B_T(r)` for every `r : ℤ`.
* Clause 3, exponent independence: `IsCanonicalScalarExtensionTateLevelMaps`
  specifies the actual Kummer power map at degree one, identity at zero,
  tensor powers at positive degrees, and dual evaluation at negative degrees.
  `scalarExtensionTateLevelIso_existsUnique` and `scalarExtensionTateLevelIso`
  give the unique signed comparison from every larger exponent `n ≥ m`.
  `scalarExtensionTateIso_exponent_naturality` states that scalar extension
  commutes with these signed Kummer comparisons, so the comparison itself is
  independent of the common annihilating exponent.
  The degree-one equations use `HEq` solely between the two existing
  presentations of the same degree-one line. Unfolding
  `coefficientTwistLine` and `coefficientTwistPower` at 1 gives the original
  `tateFiniteLine`; no new root or line object is introduced.
* Clause 4: `scalarExtensionFunctor_composition_existsUnique` quantifies
  `∃! α` and fixes its component on every K-flat `P` by conjugation through
  the actual derived counits with `DerivedCategory.Q.map (reductionBalance ...)`.
  The imported `reductionBalance_exists` specifies precisely
  `c tensor (b tensor p) ↦ c*g(b) tensor p`, the paper's
  `(p tensor b) tensor c ↦ p tensor g(b)c` in the library's scalar-first order.
  Its inverse inserts 1. `scalarExtensionFunctor_ringMap_comp` identifies
  the composed constant-sheaf map with the specified `g.comp f`.
  `scalarExtensionFunctor_composition` selects this uniquely normalized α.
* Clause 4, naturality: `scalarExtensionFunctor_composition_naturality`
  is an equation for that selected α and every `v : K ⟶ L`, with no
  existentially chosen isomorphism in the conclusion.
* Clause 4, units and coherence: `scalarExtensionFunctor_identity_existsUnique`
  specifies the identity unitor by the multiplication chain map on every K-flat
  representative. `scalarExtensionFunctor_identity` selects that unique unitor.
  The first conjunct of `scalarExtensionFunctor_coherence` identifies α for
  `g = RingHom.id B` with this unitor at `K_B`. The second conjunct quantifies
  every fourth ring `D`, map `h : C →+* D` and derived object `K`, and equates
  the two composites collapsing three successive extensions. This is the
  associativity coherence diagram, with the usual unit identifications.

Dependency declarations read and reused:

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`.
* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: `proEtaleDerivedCategory`.
* `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf` publicly retains
  `Sheaf.Paper.ProEtaleConstructibleSheaf.IsConstructibleProEtaleModuleSheaf`
  (declaration namespace `AlgebraicGeometry.Scheme`); it also supplies the
  recorded larger-coefficient predicate. We use its retained exact small-ring
  interface, with the finite-stratification and finite-stalk conditions unchanged.
* `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude` publicly retains
  `Scheme.HasProEtaleTorAmplitude` and `HasFiniteProEtaleTorAmplitude` from
  `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`. Their endpoints are exactly
  `proEtaleDerivedCategory`; the coefficient-sized-model generalization is not
  needed for A in Type u.
* `Sheaf.SixFunctors.IntrinsicDerivedTensorOfUniverses`:
  `SheafOfModules.ringedSiteDerivedTensorOfUniverses`;
  `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension`:
  `SheafOfModules.constantCoefficientScalarExtension`.
* `Sheaf.SecSmoothPurity.OpenScalarExchange`: `ProEtale.scalarExtension`;
  `Sheaf.Paper.FourCorners`: `proEtaleRingExtension`, its object formula,
  and `proEtaleRingDerivedExtension`;
  `Sheaf.Paper.AdicCoefficientDatum`: `reductionScalarComplexCounit`,
  `reductionChangeComplex`, `reductionTensorSection`, `reductionBalance`,
  its unique pure-tensor formula, naturality and cocycle.
* `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityTransition`;
  `Sheaf.Paper.TateTwistLocallyFree`: `tateFiniteLine`, `tateFiniteTensor`,
  `tateTwist_locallyFree`; its current source was also read with
  `scompile.py --source Sheaf.Paper.TateTwistLocallyFree`.
* `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`:
  `siteSheafTensorTmul` and the existing sheaf tensor;
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`: `homObj`;
  `Sheaf.Paper.CoefficientTwistsDetailed`: `coefficientTwistLine`,
  `coefficientTwistPower`, which use exactly those powers and duals.
* All recorded proof-dependency modules are imported. In particular the proof
  docstrings refer to the K-flat resolution, change-of-rings, stratum comparison,
  locally constant tensor, finite stalk, local sheafification, bounded-flat,
  invertible tensor/dual base-change and K-flat-localization descent interfaces.
  `Sheaf.Paper.SfScalarExtensionComposition` was read for its unique-normalization
  pattern; it is not imported because the integral/rational coefficients differ.

Searches retained and repeated:

* `msearch.py ... leanfinder "derived scalar extension preserves constructible
  finite Tor amplitude over finite rings and Tate twists"`: eight generic derived
  linearity, Tor, and flat module hits, no matching combined statement.
* `msearch.py ... loogle "DerivedCategory, scalarExtension, proEtale"`: zero
  hits; `scalarExtension` unknown to that service.
* `msearch.py ... grep "scalarExtensionFunctor|proEtale.*scalar.*(Comp|Tate)"
  CategoryTheory`: zero hits.
* `rg` for `scalarExtensionFunctor` and the node id in the upstream
  `WeilConjectures/` tree found no declarations. `rg` in shared `lean/Sheaf`
  found no landed declaration under this new name. Concept searches found the
  reused functor, the balanced tensor chain map, the generic tensor/dual
  comparison, and integral/rational comparisons. None covers all four clauses
  for arbitrary finite torsion rings on arbitrary schemes.

Edge cases checked: the empty scheme, zero coefficient rings, zero complexes,
zero modules, an arbitrary shift or single-degree K-flat representative, `a=b`,
non-flat coefficient maps such as Z/ell^2→Z/ell, and repeated equal rings with
nonidentity endomorphisms. Tate degrees 0, 1, -1, positive and negative powers
are explicit in the normalizations; the common exponent starts at 1, and
`m=n` is allowed in exponent independence. The invertibility assumption excludes
Spec F_ell for the Tate example. The unitor applies to the identity map itself,
not to every endomorphism of an equal endpoint ring.

No new node, dependency-module replacement, statement correction, or disputed
statement is needed. The inherited stage-1 corrections remain unchanged.

## Second reading by NH

Worker self-check of this repair, not a claim of an independent agent reading:
I reopened the node and the repaired file and matched each hypothesis and every
clause above. The returned K-flat assertion formerly did not mention the functor
in its conclusion; it now has an explicit counit isomorphism computing S_f(Q P).
The entire constructible/Tor clause and the line/Tate clauses, including signed
degrees and exponent independence, are now present. Composition is selected from
an existence-and-uniqueness characterization by the published balanced map.
Naturality, the g=id unitor law and the four-ring coherence equation refer to
that selected comparison. Every theorem docstring now gives its source and
proof steps. No theorem is proved in the delivered module. The maintainer's
independent immutable-head review remains the external second reading.
