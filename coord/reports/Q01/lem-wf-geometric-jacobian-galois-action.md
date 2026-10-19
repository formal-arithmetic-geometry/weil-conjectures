## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.GeometricJacobianGaloisAction` states
`AlgebraicGeometry.existsUnique_geometricJacobian_galoisAction`. Its sole proof is `sorry`.
There are no new definitions, auxiliary assertions, dependency replacements or statement changes.
Only the item's `lean` field changes. The stage-1 variance-corrected statement and proof
are preserved verbatim. The extracted node has no `statement_change` field; the prior
correction is documented by its `split_report`, stage-1 report and recorded review.

Sources read: the item's full DAG statement and six proof steps; its master blueprint file
`literature/blueprint/master/blueprint/sec-purity-real-sheaves/sk-d-real-jacobian/lem-wf-geometric-jacobian-galois-action.md`;
the corresponding main-20261015 file; and the main-20261015 statement of
`thm-pd-jacobian-general-field`. The theorem follows the corrected DAG: the scheme action
lies over `Spec (σ⁻¹)`, whereas points are twisted by `Spec σ`.

Hypotheses, matched individually:

- The field `k₀` is `(k₀ : Type u) [Field k₀]`.
- An algebraic closure is `(K : Type u) [Field K] [Algebra k₀ K]
  [IsAlgClosure k₀ K]`. The explicit `[IsAlgClosed K]` exposes the algebraically closed
  field structure already implied by `IsAlgClosure`; it is required by the upstream canonical
  `pointsAddEquivGeometricPoints` interface and imposes no additional mathematical condition.
- `C₀/k₀` is `(C₀ : Scheme.{u}) [C₀.Over (Spec (.of k₀))]`.
  Its smooth projective geometrically connected curve hypotheses are
  `[SmoothOfRelativeDimension 1 (C₀ ↘ Spec (.of k₀))]`,
  `[IsProper (C₀ ↘ Spec (.of k₀))]` and
  `[GeometricallyConnected (C₀ ↘ Spec (.of k₀))]`. Proper smooth curves over a field
  are projective; this is the same proper/relative-dimension-one convention as the supplied
  general-field Jacobian declaration and the current source statement for it.
- `C=C₀×K` is an arbitrary cartesian presentation `(C : Scheme.{u})`, its `Over K`
  structure, `(p : C ⟶ C₀)` and `hC : IsPullback p ... (Spec.map (algebraMap k₀ K))`.
  The explicit `IsCurve`, `Smooth`, `SmoothOfRelativeDimension 1`, `IsProper` and
  `GeometricallyIntegral` instances on C are the consequences of this base change already
  used to type `IsJacobian`, `picardZero`, and `picardFunctorDegree`. They add no restriction
  on C₀: a smooth geometrically connected curve is geometrically integral, and these
  properties persist after base change.
- The fixed Jacobian is `(J : Over (Spec (.of K))) [CommGrpObj J]
  [IsJacobian (C ↘ Spec (.of K)) J]`. A Jacobian's group law is commutative; the explicit
  commutative structure also supplies the abelian group of points used in the Tate module.
- The FIXED representing isomorphism is the binder
  `φ : (picardFunctorDegree (C ↘ Spec (.of K)) 0).obj.RepresentableBy J`, with
  `hφ : IsPicardZeroMul ... φ`. Although `IsJacobian` only asserts existence of such a
  representation, these two binders fix the one in the node's pair `(J,φ)`. There is no
  rational point assumption on C₀ or C.
- `Γ` is `K ≃ₐ[k₀] K`, with its existing multiplication by composition. All types share the
  explicit universe `u`; there is no independent smaller test-scheme universe.

Conclusions, matched individually and in order:

1. Canonical left semilinear action: the outer `∃! a` quantifies over
   `(σ : K ≃ₐ[k₀] K) → SemilinearGrpHom
   (Spec.map (CommRingCat.ofHom σ.symm.toAlgHom.toRingHom)) J J`.
   `SemilinearGrpHom.w` is the square over `b_σ`; `mul_comp` is semilinear preservation of
   the group law. With `IsIso (a σ).hom`, this also preserves identity and inverse in the
   semilinear sense. The next two clauses give `(a 1).hom = 𝟙 J.left` and
   `(a (σ*τ)).hom = (a τ).hom ≫ (a σ).hom`. Because `≫` composes left to right, this is
   precisely `a_{στ}=a_σ∘a_τ`. Uniqueness is relative to the fixed φ.
2. Ground-field model and representing comparison: `∃ J₀, ∃ (_ : CommGrpObj J₀), ∃ r₀`
   provides the ground-field representation, `IsPicardZeroMul`, properness, smoothness of
   relative dimension `arithmeticGenus k₀ C₀`, and geometric integrality, exactly as in
   `exists_jacobian_descent`. The map `q` and `hJ : IsPullback q J.hom J₀.hom ...` give
   `α=hJ.isoPullback : J.left ≅ J₀×K`.
3. The comparison respects the representing isomorphisms, rather than choosing an arbitrary
   isomorphism of schemes. The first clause following hJ quantifies over EVERY K-test scheme
   T and EVERY fibrewise-degree-zero class L on `C₀×T`. It compares the φ-classifying map
   of the pullback along `(pullbackIsoOfIsPullback hC T).hom`, composed with q, with the
   r₀-classifying map of L. The terms `toSheafify` are the actual canonical maps to the
   degree-zero Picard fppf sheaves. This is the unit characterization of the representing
   base-change comparison, including classes which are only represented locally fppf.
4. The displayed conjugation formula is
   `hJ.isoPullback.inv ≫ (a σ).hom ≫ hJ.isoPullback.hom =
   baseChangeMap J₀.hom (specAlgEquivOver σ.symm)`.
   The right side is the existing construction of `id_{J₀}×b_σ`.
5. Left action on K-points: `ρ` is a monoid homomorphism into
   `Multiplicative (AddAut (Additive (𝟙_ (Over (Spec (.of K))) ⟶ J)))`.
   Mathlib writes composition of `AddAut` additively, so `Multiplicative` is essential.
   The equation `((ρ σ).toAdd x).toMul.left = Spec.map σ ≫ x.toMul.left ≫ (a σ).hom`
   is exactly `σ·x=a_σ∘x∘s_σ`. The target consists of additive automorphisms, so J(K)
   is a Γ-module, including its identity and composition laws.
6. Canonical Picard identification: `Φ : Additive (picardZero K C) ≃+ J(K)`.
   For every L, the equation involving `φ.homEquiv (Φ L).toMul` and `toSheafify` fixes Φ
   to be the identification induced by the given representation, using the canonical
   projection from `C×_K Spec K` to C. This excludes an arbitrary abstract group isomorphism.
7. Model point comparison: `Φ₀` is an additive isomorphism from Pic⁰(C) to
   `Additive (Over.mk (Spec.map (algebraMap k₀ K)) ⟶ J₀)`.
   `(Φ₀ L).toMul.left = (Φ L).toMul.left ≫ q` identifies J(K) with J₀(K).
   The next equation says the action on these model points is precisely
   `specAlgEquivOver σ ≫ (Φ₀ L).toMul`, i.e. `u↦u∘s_σ`.
8. Picard equivariance: for each σ, `∃ γ : C ⟶ C` with `γ≫p=p` and
   `γ≫structure=structure≫Spec.map σ` determines `γ=id_{C₀}×s_σ` by the cartesian square.
   `(Φ.symm ((ρ σ).toAdd (Φ L))).toMul.1 = Pic.map γ L.toMul.1`
   is the specified pullback action on Pic⁰(C), for every L.
9. All prime-power torsion: for each prime ℓ and n≥1 the additive equivalence e has source
   `AddSubgroup.torsionBy (Additive J₀(K)) ((ℓ : ℤ)^n)` and target the same subgroup of
   `Additive (picardZero K C)`. The equation `(e z).1=Φ₀.symm z.1` identifies ALL levels
   as restrictions of the same underlying comparison. Its equivariance is explicitly stated
   for z,z' with `z'.1.toMul=specAlgEquivOver σ≫z.1.toMul`, and its multiplication-by-ℓ
   compatibility is explicitly stated for levels n+1 and n whenever `z'.1=(ℓ:ℤ)•z.1`.
   The latter uses Φ₀.symm at level n+1; the restriction equation makes it the same as e
   at that level, so it gives the full transition square, not unrelated levelwise isomorphisms.
10. Integral Tate action: for EVERY prime ℓ, R is a monoid homomorphism into the group of
    `ℤ_[ℓ]`-linear automorphisms of `AddCommGroup.tateModule ℓ (Additive J(K))`.
    `(R σ t).1 n=(ρ σ).toAdd (t.1 n)` specifies the componentwise action.
    A monoid homomorphism to linear automorphisms is precisely a linear Γ-action, equivalently
    a `ℤ_[ℓ][Γ]`-module structure; it includes both scalar commutation and the action laws.
11. Abelian-variety Tate comparison: only the final clause assumes `[CharP k₀ c]` and ℓ≠c.
    R' acts on the existing `IsAbelianVariety.tateModule ℓ J`, and its action intertwines R
    under the explicit canonical linear equivalence
    `AddCommGroup.tateModule.congr (IsAbelianVariety.pointsAddEquivGeometricPoints J)`.
    Thus it is the same inverse-limit action under the canonical identification, not merely
    an unspecified isomorphism of Tate modules.

Dependency declarations read and reused:

- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian`:
  `AlgebraicGeometry.IsJacobian`, full class signature, docstring, dimension and representing fields.
- `WeilConjectures.AlgebraicGeometry.Picard.Jacobian` (publicly imported by the first module):
  `AlgebraicGeometry.exists_jacobian_descent`, full signature and docstring;
  `IsPicardZeroMul`, `specAlgEquivOver`, and the representing/Picard comparison interfaces.
  The theorem's model clauses use the same r₀ interface and the stated geometric properties.
- `WeilConjectures.GroupTheory.TateModule` (publicly imported by the Tate module):
  `AddCommGroup.tateModule`, its coordinate and transition equations, p-adic scalar action,
  `AddCommGroup.tateModule.congr`, and the recorded `rationalTateModule` definition.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`:
  `AlgebraicGeometry.IsAbelianVariety.tateModule`, `SemilinearGrpHom`,
  `IsAbelianVariety.pointsAddEquivGeometricPoints`; full signatures and docstrings read.
- Proof dependency import `WeilConjectures.Mathlib.CategoryTheory.Yoneda`:
  `CategoryTheory.Functor.RepresentableBy.existsUnique_iso`, including its exact triangle.
- Proof dependency import `Mathlib.CategoryTheory.Functor.FullyFaithful`:
  `CategoryTheory.Functor.FullyFaithful.isoEquiv`, with
  `CategoryTheory.Yoneda.fullyFaithful` from Mathlib's Yoneda module. Both signatures read.

Edge checks: genus zero has the trivial Jacobian and trivial point/Tate actions; no positive
Jacobian-dimension hypothesis is imposed. Characteristic zero is covered by c=0, and characteristic
ℓ is INCLUDED in the torsion and integral Tate assertions; only the final comparison is conditional.
The unit automorphism, arbitrary products of automorphisms and noncommuting automorphisms obey the
corrected variance: Spec reverses composition, so `Spec (στ)` is `Spec τ ∘ Spec σ`;
using inverse automorphisms makes the actual Lean action law `a τ ≫ a σ`. Directly on an elliptic model the point formula gives
coordinate action `(x,y)↦(σ x,σ y)`. No k₀-rational point is assumed. The geometric connectedness
and relative dimension one exclude the empty curve as in the source; no new nonempty hypothesis
is inserted. Level n=1 is included, the inverse limit's n=0 coordinate is the forced zero coordinate,
and all transition equations are kept. Algebraic closures already equal to the ground field are
included. Arbitrary cartesian presentations of C and J are permitted, not only chosen pullbacks.

Searches actually run through `/home/ubuntu/weil-launcher-nt/msearch.py`:

- LeanFinder: `The geometric Jacobian has a semilinear Galois action compatible with Picard group
  and Tate module`. Eight hits, including `galRestrict`, Hilbert 90, `CommRing.Pic.mapAlgebra`,
  `IsGaloisGroup.to_isFractionRing`, and absolute Galois abelianization; no matching scheme theorem.
- Loogle: `AlgebraicGeometry.IsJacobian, "galois"`. Zero hits; service reports unknown identifier
  `AlgebraicGeometry.IsJacobian` (the upstream project identifier is not indexed there).
- grep: `Jacobian.*[Gg]alois|[Gg]alois.*Jacobian|[Ss]emilinear`, subdirectory AlgebraicGeometry.
  Four hits, all in `Mathlib/AlgebraicGeometry/StructureSheaf.lean`, involving `toSemilinearMap`;
  no matching Jacobian theorem.
- LeanSearch: `A geometric Jacobian has a canonical semilinear Galois action on its points and
  Tate module`. Eight hits: Weierstrass Jacobian definitions, its point group, Galois-category
  actions and polynomial Galois actions; none states this node.

Additional direct searches: `rg` for Galois/semilinear/geometric-Jacobian declarations in upstream
AbelianVariety and Picard modules and side `lean/Sheaf`; node-id grep across upstream
`WeilConjectures` (no hit); Jacobian-name entries in `dag/lean_names_upstream.json`; exact-name
`rg` for the proposed declaration across Mathlib, upstream, side modules and the name index
(no hit). The upstream `SemilinearGrpHom` and Tate constructions were found and reused, not copied.
The side `JacobianBaseChangeCompatible` module was read: it has algebraically closed base-field
hypotheses and states a comparison for a different DAG node, not the present full action assertion.
No missing independent notion or unusable dependency record was found.

Validation: `scompile.py Q01 lem-wf-geometric-jacobian-galois-action <module>` compiles both the
sandbox form and the library-path form cleanly (about four seconds per form), within the fixed
60-second limit. All universes and variables are bound. The one local overlapping-instance linter
suppression concerns `IsCurve` versus `IsProper` in the given curve interface: `IsJacobian` requires
`IsCurve`, and the source also requires properness. No mathematical assumption is suppressed.

## Second reading by Q01

Independent maintainer reading of immutable delivery
`c698014076589e6759b90c9e46cb1c3e3086c2a5`, 2026-10-17. This section replaces the
original author's second pass. I did not write or previously second-read the delivery.

I read packet.md, the immutable item and all four statement-dependency records, the entire
Lean module, the worker report, and the exact dependency declarations and docstrings.
Source checks used the master and main-20261015 geometric-Jacobian statements, the master
proof's two paragraphs, and the general-field Jacobian statement and proof (especially
Steps 8–11). I also read the three definition sources and the prior Q114 correction report.

Hypothesis checks: `k₀`, `K`, the field and algebra instances and `IsAlgClosure` express
an arbitrary ground field and its algebraic closure. `IsAlgClosed K` is a consequence,
not a stronger assumption. The proper, smooth-relative-dimension-one, geometrically
connected C₀ is exactly the source curve convention; a smooth proper curve over a field
is projective. `p,hC` specify the actual base change. The explicit properties of C follow
from that square and C₀'s hypotheses: smoothness gives geometric reducedness, and a smooth
geometrically connected curve is geometrically irreducible. Properness and finite type
give `IsCurve`. `IsJacobian` supplies the abelian variety and genus condition; `φ,hφ`
fix the representing isomorphism with its group compatibility. `CommGrpObj` records the
abelian group law. There is no rational-point, perfect-field or invertibility assumption.
The universe `u` is explicit throughout; test schemes use the same scheme universe and
the actual Picard functor has values in `Type (u+1)`. No smaller independent test universe
or forced equality of site object and morphism universes is introduced.

Conclusion checks:

- `SemilinearGrpHom.w` and `mul_comp`, with `IsIso`, express semilinear group
  isomorphisms over `Spec σ⁻¹`, including unit and inverse preservation. The explicit
  identity and `a τ ≫ a σ` product clauses give the correct left action.
- The model J₀ has a genuine degree-zero Picard representation and the expected geometric
  properties. The cartesian square `hJ` gives the representing comparison α. Its equation
  on every test scheme and presheaf class uses the canonical sheafification unit and the
  actual base-change isomorphism. Because these classes locally generate the sheaf, this
  determines the representing comparison, rather than permitting an arbitrary map.
- `hJ.isoPullback.inv ≫ a σ ≫ hJ.isoPullback.hom` is α aσ α⁻¹. Its right side is
  the existing `baseChangeMap` for `specAlgEquivOver σ.symm`.
- The monoid homomorphism ρ gives additive point automorphisms with the required formula
  `Spec σ ≫ x ≫ a σ`. Φ is fixed by the given φ and the canonical Picard sheafification
  map. Φ₀ is fixed by q, and its next equation is exactly precomposition by `Spec σ`.
- The two projection equations determine γ as `id_C₀ × Spec σ`; the subsequent equality
  is the specified Picard pullback equivariance for every line-bundle class.
- For every prime and n≥1, e is precisely the restriction of Φ₀.symm to torsion.
  Its equivariance equation and its adjacent-level equation give the full torsion and
  multiplication-by-ℓ compatibility. The level n+1 map is the same restriction of Φ₀.symm.
- R is a homomorphism to ℤ_[ℓ]-linear automorphisms of the existing group Tate module,
  specified at every coordinate. This is the claimed group-ring module structure.
  The final R' intertwines R through the canonical point/geometric-point Tate equivalence;
  only this clause requires ℓ different from the characteristic.

Dependency checks opened `IsJacobian` in AbelianVariety/Jacobian.lean:62–70;
`IsPicardZeroMul`, `specAlgEquivOver` and `exists_jacobian_descent` in
Picard/Jacobian.lean:383,1637,2069; `SemilinearGrpHom`,
`IsAbelianVariety.tateModule` and `pointsAddEquivGeometricPoints` in
AbelianVariety/TateModule.lean:70,130,174; and `AddCommGroup.tateModule`, its scalar action,
`map` and `congr` in GroupTheory/TateModule.lean. The actual declarations match the
notions used. Representing uniqueness and fully faithful Yoneda interfaces were opened
as well. The generic uniqueness theorem's group compatibility is obtained from φ and hφ;
it is not a separate assumption or a claim that type-valued Yoneda alone preserves groups.

Independent rg searches used semilinear/Galois/Jacobian terminology in Mathlib's algebraic
geometry sources, upstream WeilConjectures and the side Sheaf tree. Existing generic
semilinear and Tate interfaces are reused, and no declaration states the complete item.
The worker records LeanSearch, LeanFinder/Loogle and grep searches with results.
There are no new definitions or helper modules, hence no hollow construction or duplication.

Edge checks include genus zero, trivial Γ, noncommuting automorphisms, characteristic zero,
imperfect k₀, ℓ equal to the characteristic in the torsion and integral Tate clauses,
n=1, the forced zero n=0 Tate coordinate, and arbitrary cartesian presentations.
Empty curves are excluded already by geometric connectedness. Spec reverses composition:
using σ⁻¹ on schemes and σ on points is necessary even for the zero Jacobian. The prior
source correction is mathematically justified and predates this stage-2 change.
I opened the dual-Tate and finite-field-no-fixed citers: their coordinate action and fixed
vector conclusions survive. The latter's old scheme notation remains a downstream issue,
not a change made or needed to the present statement.

Validation was independently reproduced with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q01
lem-wf-geometric-jacobian-galois-action
snapshot/lean/Sheaf/AlgebraicGeometry/AbelianVariety/GeometricJacobianGaloisAction.lean`.
The wrapper returned exit 0: sandbox form 3.3 s, library form 3.5 s, no diagnostics.
The current wrapper dispatches its private overlay compile to the server; no direct ssh
command or global build was run. The node's full `lean.statement` equals the source signature
verbatim. All lines are at most 100 characters, the sole local theorem ends in `by sorry`,
and both module and declaration docstrings identify the source and blueprint. The two
ordinary imports support the stated proof dependencies. No live Lean or project clone was
edited. No pro-etale replacement is used or relevant.

Findings: no mathematical or Lean-record repair is needed. The report required an independent
second-reading section (H11 / brief §6); the original section explicitly described the author's
own second pass. This replacement supplies the completed independent reading. It also corrects
the worker report's inaccurate reference to an existing `statement_change` field. No node or
Lean module is changed.
