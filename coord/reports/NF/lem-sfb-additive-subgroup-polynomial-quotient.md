## Worker report

The delivery states `AlgebraicGeometry.StandardGroupSchemes.exists_additiveSubgroup_polynomial_quotient`
in `Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient`. Its only theorem has
proof `sorry`. Eight helper definitions have actual data: polynomial substitution,
affine coordinate points, pullback of the multiplicative coordinate, restriction's
kernel ideal, subgroup translation, its pointwise coset coequalizer, its fppf
sheafification, and the coset projection. They specialize existing constructions to
the objects of this theorem; they introduce no separate independent mathematical notion.

The live node has an accepted stage-1 split and no Lean attachment. The inherited
BLOCKED ending concerned a stage-1 re-split, not this stage-2 assignment. The stage
handoff at the start of `coord/brief-stage2.md` explicitly distinguishes these. The
queue lists the item at stage 2. This delivery changes only the item's `lean` field;
it preserves its statement, dependencies, seven proof steps and accepted review.
There was no saved Lean or node file in the inherited sandbox.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `variable (k : Type u) [Field k]`, with universe `u` explicitly declared. |
| The specified additive and multiplicative groups | Existing `additive k`, `multiplicative k`, `affine k R`, and their recorded group structures from `StandardGroupSchemes`. No replacement group laws. |
| Closed subgroup N inside Gₐ | `N : Over (Spec (.of k))`, `[GrpObj N]`, `i : N ⟶ additive k`, `[IsClosedSubgroupScheme i]`. The upstream class includes both the subgroup homomorphism condition and closed immersion of `i.left`. |
| Proper subgroup | `hproper : ¬ IsIso i`. For a closed immersion, being the whole subgroup is precisely being an isomorphism onto Gₐ; this excludes equality up to its specified inclusion, not only equality of carriers. |
| A monic polynomial P of positive degree n | `∃ P : Polynomial k, P.Monic ∧ 0 < P.natDegree ∧ ...`. Throughout, `n` is `P.natDegree`. |
| Principal ideal equal to the defining ideal | `Ideal.span ({P} : Set (Polynomial k)) = additiveSubgroupDefiningIdeal k i`. The latter is the kernel of `k[T] → Γ(N,O)` obtained by the canonical `ΓSpecIso` and `i.left.appTop`. This retains nilpotent scheme structure. |
| Uniqueness of the monic generator | `∀ Q : Polynomial k, Q.Monic → Ideal.span {Q} = additiveSubgroupDefiningIdeal k i → Q = P`. This is uniqueness among all monic generators, not merely among those satisfying the subsequent conclusions. |
| P(0)=0 | `P.eval 0 = 0`. |
| P(X+Y)=P(X)+P(Y) in k[X,Y] | The displayed `P.eval₂ MvPolynomial.C` identity in `MvPolynomial (Fin 2) k`, with variables `MvPolynomial.X 0` and `MvPolynomial.X 1`. This is a polynomial identity, not an assertion about k-rational points. |
| Morphism defined on R-points by evaluation | `additivePolynomialMap k P := map k (Polynomial.aeval P)`. Contravariant affine Spec sends the coordinate substitution `T ↦ P(T)` to precisely that morphism. `additiveCoordinatePoint` uses `Polynomial.aeval x`. |
| A group-scheme homomorphism | `IsMonHom (additivePolynomialMap k P)`. |
| Faithfully flat in the specified module sense | `(Polynomial.aeval (R := k) P).toRingHom.FaithfullyFlat`. Mathlib defines this as `Module.FaithfullyFlat` for the target through the coordinate ring map's algebra structure. Thus this is not replaced by mere surjectivity or geometric flatness. |
| Globally finitely presented | `LocallyOfFinitePresentation ...left ∧ QuasiCompact ...left ∧ QuasiSeparated ...left`, the conjunction described by the dependency node. |
| Scheme-theoretic kernel is N | `∃ e : N ≅ GrpObj.ker (additivePolynomialMap k P), e.hom ≫ GrpObj.kerι ... = i`. The kernel is the actual pullback of the identity section, and its inclusion is identified. |
| Fppf sheaf quotient Gₐ/N | `additiveSubgroupCosetPresheaf` is the presheaf coequalizer of translation `(z,x) ↦ i(z)+x` and projection `(z,x) ↦ x`; colimits of presheaves of sets are pointwise. Its value on Spec R is R/N(R). `additiveSubgroupFppfQuotient` applies the recorded `presheafToSheaf` for `Scheme.fppfTopology.over (Spec (.of k))`. |
| The polynomial induces the quotient isomorphism | The existential sheaf isomorphism `e` has source this actual sheafification and target the sheafified lifted representable of Gₐ. Its equation says that composing the sheafified coset projection with `e.hom` equals the sheafified Yoneda map of the polynomial. This specifies the induced isomorphism, not an unrelated abstract isomorphism. The fppf topology is subcanonical, so the target is canonically the represented sheaf Gₐ. Since the defining polynomial map is `IsMonHom`, the descended isomorphism preserves addition. |
| G affine of finite type | The final clause quantifies `G : Over (Spec (.of k))`, `[GrpObj G]`, `[IsAffine G.left]`, `[LocallyOfFiniteType G.hom]`, `[QuasiCompact G.hom]`. |
| η:G→Gₘ a homomorphism | `(eta : G ⟶ multiplicative k) [IsMonHom eta]`. |
| Scalar stability of N on every k-algebra | The antecedent quantifies `(R : Type u) [CommRing R] [Algebra k R]`, `g : affine k R ⟶ G`, `x : R`. A lift `z` through `i` of the point with coordinate x must yield a lift of the point with coordinate `multiplicativeCoordinateValue k (g ≫ eta) * x`. The latter coordinate is obtained by the fully faithful algebraic Spec functor's preimage applied to the actual point, evaluated at the Laurent coordinate t. It is automatically a unit. |
| Scalar formula on all R,g,x | The consequent again quantifies every test algebra, g and x and asserts `Polynomial.aeval (multiplicativeCoordinateValue k (g ≫ eta) * x) P = multiplicativeCoordinateValue k (g ≫ eta) ^ P.natDegree * Polynomial.aeval x P`. There is no restriction to fields, reduced rings or rational points. |
| The quotient action is through ηⁿ | This is the same scalar identity transported through the specified quotient isomorphism: the source point's scalar translate maps to η(g)ⁿ times its image. The canonical comparison equation fixes the identification under which this assertion holds. |

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine`, `map`, `additive`,
  `additiveGroup`, `multiplicative`, `multiplicativeGroup`; the additive structure
  is fixed by `additiveGroup_existsUnique`, including all three coordinate maps.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`; `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`;
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `GrpObj.ker`,
  `GrpObj.kerι`. The last two use the pullback of the identity section.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  supplied by the closed subgroup class.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`;
  `Mathlib.Algebra.Polynomial.AlgebraMap`: `Polynomial.aeval`.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`,
  `Scheme.fppfTopology`, including flat locally finitely presented covers;
  `Mathlib.CategoryTheory.Sites.Over`: the slice topology.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf` and its
  adjunction; `ConcreteSheafification` provides the actual instance.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`; global finite presentation includes the recorded
  quasi-compact and quasi-separated clauses.

Every recorded statement dependency has a usable existing declaration. No dependency
module or new DAG node was needed. Available proof-dependency modules are imported
for the recorded proof plan, including polynomial PID, monic quotient basis,
faithful-flat spectrum surjectivity, flat affine morphisms, and affine separation.
The proof-only nodes `lem-sfb-monic-quotient-faithful-tensor-coordinates` and
`lem-a1-fppf-kernel-pair-quotient-descent` currently have neither a Lean module nor a
Mathlib match, so there is no module of those nodes to import; they remain cited in
the complete seven-step theorem docstring and untouched `proof_deps`.

Edge cases checked before and after writing:

- N=0 gives the monic polynomial T, degree one, identity quotient; this case is included.
- In characteristic zero every proper subgroup is this case; no positive-characteristic
  assumption or algebraic-closedness assumption was added.
- In characteristic p, α_p gives T^p, retaining its nonreduced kernel.
- The constant subgroup F_p gives T^p-T. Stability forces the necessary relation on
  the scalar, so the exponent n=p formula remains correct.
- N=Gₐ is excluded by properness, as required; a constant monic generator would give
  an empty closed subscheme and cannot contain the identity. Thus degree zero is excluded.
- Test algebras may have nilpotents or be the zero ring. The scalar formula is an
  identity in the test algebra, and the monic quotient argument works in both cases.
- The trivial character and trivial group are included. No property of η beyond
  being a homomorphism and preserving the specified subgroup is assumed.
- Lifted Yoneda values are `Type (u+1)` on the big site of `u`-small schemes;
  this provides genuine sheafification without imposing an additional size hypothesis.

Source read directly: `literature/milne-algebraic-groups_iAG2017.pdf`, Exercise
14-3(a), p.301 (the exact sequence), Example 14.40, pp.292-293 (additive polynomial
identity), and Theorem 15.34(d), p.319 (the equivariant sequence). The seven-step
argument and monic scalar normalization are the accepted node's existing proof,
retained without change and transcribed into the declaration docstring.

Searches for an existing statement and duplicate names:

- `msearch.py ... leanfinder` with “A proper closed subgroup scheme of the additive
  group over a field is the kernel of a unique monic additive polynomial; faithfully
  flat quotient and scalar equivariance”: eight unrelated kernel-ideal and polynomial
  quotient hits; no classification or scalar-equivariant quotient theorem.
- `msearch.py ... loogle` with `Polynomial.Monic, IsClosedSubgroupScheme,
  RingHom.FaithfullyFlat`, and the narrower `Polynomial.Monic, RingHom.FaithfullyFlat`:
  zero hits.
- `msearch.py ... grep` with `additive.*[Pp]olynomial|[Pp]olynomial.*additive`, in
  `AlgebraicGeometry` and `Algebra/Polynomial`: no matching classification; the latter
  found only the comment that monomials generate the additive monoid of polynomials.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for additive-polynomial/subgroup
  combinations and the exact item id: no statement of the item. Existing standard
  group-scheme and general quotient constructions were read and reused through their
  native constructions, rather than replacing the group schemes or topology.
- `rg` for every introduced full name in Mathlib, both project source roots, and
  `dag/lean_names_upstream.json`: no pre-existing declarations with these names.

Validation: `scompile.py NF lem-sfb-additive-subgroup-polynomial-quotient` compiled
both its sandbox module and its final library module cleanly (7.1 s and 4.9 s,
respectively). No errors or warnings. All source edits are confined to the authorized
sandbox. No global build, direct repository Git command, or live-source write was used.

No `STATEMENT-DISPUTED` finding, statement correction, or node fault remains.

## Second reading by NF

Fresh clause-by-clause audit by this worker against the live node and complete
module: all hypotheses and conclusions are accounted for in the table above.
In particular the ideal uses the restriction kernel, the kernel is identified
with its inclusion, the isomorphism is forced to be induced by the polynomial,
and scalar stability and its conclusion both quantify all test algebras. The
accepted node and split were preserved. Compilation repaired only API issues:
use the explicit fully faithful Spec witness for coordinate recovery, open the
existing monoid-object scope for translation, specify the base of `aeval`, and
spell the homomorphism binder `eta` to avoid the scoped identity-section token.
No statement was weakened. No other agent was started, as the dispatch brief
requires; the maintainer supplies the independent review of this delivery.
