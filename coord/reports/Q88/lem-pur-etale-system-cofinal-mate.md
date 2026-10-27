## Worker report

Item: `lem-pur-etale-system-cofinal-mate`. The module is
`Sheaf.Paper.EtaleSystemCofinalMate`, with main declaration
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemCofinalMate` and the
local-field specialization `etaleSystemCofinalMate_localField` in the same
namespace. This delivery states the mathematics and supplies actual canonical
helper constructions; theorem proofs alone are postponed. Every helper belongs
to the cofinal-comparison construction described by this node. No independent
notion, dependency repair, or statement correction is introduced.

Source checked: Zheng, *Six operations and Lefschetz–Verdier formula for
Deligne–Mumford stacks*, Construction 4.1, printed p. 21, the discussion before
Lemma 4.10 on p. 23, and the adjunction argument of Lemma 5.22 on p. 36.
Also read the current blueprint's exceptional-inverse-image definition, including
its integral coefficient-system construction. The node explicitly supplies the
finite-block extension and canonical map formulas used here.

### Hypotheses and objects

- The fixed algebraic closure of the finite field and its characteristic are
  `k : WeilConjectures.FiniteFieldDatum.{u}`. The coefficient prime and its
  invertibility over the base are `l`, `hl : l.Prime`, and `hlp : l ≠ k.p`.
- `X Y : Over (Spec (CommRingCat.of k.k))` are the two schemes over that field.
  `LocallyOfFiniteType` and `QuasiCompact` on both structure maps say precisely
  finite type. The morphism `f : X ⟶ Y` is over the base, and
  `IsSeparated f.left`, `LocallyOfFiniteType f.left`, `QuasiCompact f.left`
  give its separated finite-type hypotheses. There is no separatedness
  hypothesis on Y.
- `c : Compactification f.left` fixes the same open/proper factorization
  throughout; all support functors, projections, repetition comparisons and
  mate maps depend on this c.
- `Coefficients.{u} l` is the dependency's actual inverse functor to
  `CommRingCat.{u+1}`, with a finiteness proof and a power-of-l annihilator at
  each level. `Modules W B.rings` and `Derived W B.rings` are the dependency's
  strict sequence-site module category and its ordinary unbounded derived
  category. These are not arbitrary diagrams in a derived category.
- Indices are zero based: Lean n denotes the paper level n+1. A strictly
  increasing positive sequence is `r : ℕ ↪o ℕ`. Such an embedding is automatically
  unbounded, so this encoding loses no unboundedness hypothesis. The ramified
  sequence n↦en becomes `cofinalRamification e he`, whose function is
  `n ↦ e*(n+1)-1`.

### Each conclusion and its maps

1. `cofinalCoefficients` reindexes the actual coefficient functor, including its
   maps. `cofinalSite`, `cofinalRing` and `cofinalRestriction` construct
   restriction on module sheaves on the ringed sequence site. The structural
   ring map is `eqToHom` of the literal selected-ring equality, rather than an
   unspecified scalar map. `cofinalRestriction_exact` supplies the exactness
   witnesses used by `cofinalU`, the actual localized restriction.
2. `CofinalEncoding` identifies this category with the dependency's
   `StrictRingSystem`, on sections, all morphisms and horizontal transitions.
   `CofinalExtension.model` uses its `SystemDerivedLeftExtension`, including
   ordinary and derived adjunctions, the universal left-derived comparison,
   and computation on K-flat representatives. Its `ordinary` field identifies
   the ordinary functor with the dependency's selected extension. Consequently
   the transitions, including equal least indices, are the recorded ones,
   using its canonical tensor associators.
3. The least-index function is `SheafOfModules.systemNextSelected r m`.
   `CofinalExtension.level` states the actual natural isomorphism
   e_m L_r = (derived constant-ring extension) e_t(m). The scalar map is
   literally `B.rings.map` of m≤r(t(m)). `ordinaryLevel_unit` fixes its ordinary
   adjunct by the selected system unit followed by the system transition.
   `level_normalization` fixes its derived comparison by the canonical
   comparison on all cochain representatives. `Evaluation.cofinalComplex`,
   `Evaluation.cofinalFactor` and `cofinalLevelComplex` are real termwise
   constructions used in this equation. The scalar functor is the existing
   `scalarExtension`, with `scalarExtensionRepresentative`; it is not replaced
   by an arbitrary functor satisfying an evaluated formula.
4. `projection : Theory c l` uses the recorded ordinary open extension and
   ordinary proper image, derived in that order as `Support.F`. This is F_C,
   and its `supportEvaluation` is the fixed-compactification single-ring F.
5. `cofinalRepeated` is D_m=C_(r(t(m))), and `cofinalCoefficient` is the actual
   transition map D→C. `CofinalRepeat` fixes repetition on sections, morphisms,
   and every restriction. `CofinalRepeatSupport` specifies the identity on
   sections of the ordinary open and proper comparisons.
   `CofinalRepeatSupport.kappa` is constructed from the exact-open comparison
   and the dependency's universal `blockDerivedComparison` for proper image;
   its data are not chosen from a bare existence proposition.
6. `CofinalFactor` identifies selected extension with repetition followed by
   scalar extension. `ordinary_unit` fixes the ordinary comparison by its
   adjunction transpose. `normalization` fixes the derived comparison by the
   universal derived counit on representatives. These are system equations,
   before evaluation.
7. `CofinalSupport.h` is the actual natural isomorphism F_C L_X ≅ L_Y F_Cr.
   `CofinalSupport.normalization` is its defining system equation using q for
   D→C, the two normalized factor comparisons, and canonical kappa. This is
   exactly inverse q followed by repetition, as in node proof step 2.
   `CofinalSupport.evaluation` states that its level component, through the
   fixed evaluation identifications, is inverse `compactScalarMap` for
   C_(r(t(m)))→C_m. Both clauses are retained: an equality of arbitrary system
   morphisms is never inferred just from their evaluations.
8. `cofinalMate` constructs the right comparison by Mathlib's
   `Adjunction.comp`, `ofNatIsoLeft`, and `rightAdjointUniq`.
   `CofinalSupport.rho` instantiates this construction for h and the fixed
   adjunctions a and b. Its type is the natural isomorphism
   G_C ⋙ U_X ≅ U_Y ⋙ G_Cr. There are no assumed or chosen exceptional functors:
   the main theorem quantifies over every fixed pair of functors and their
   actual support adjunctions, as the node requests.
9. The main theorem's middle conjunct states the Hom formula for every N, M
   and derived morphism z. It first inverts the X extension adjunction, then
   the C support adjunction, precomposes with h.inv, then applies the Y
   extension adjunction and the selected support adjunction. The result equals
   z followed by rho. Thus this is the entire specified Hom chain, and it
   characterizes rho uniquely. Naturality and map action are part of its
   `NatIso` type and hold on all ordinary derived morphisms.
10. The next conjunct is the explicit counit equation of node proof step 5:
    h, then L_Y F_Cr(rho), then L_Y(epsilon_r), then d_Y equals F_C(d_X),
    then epsilon_C. These are the actual system counits of the fixed
    adjunctions. Its transpose gives counit preservation after restriction.
11. `CofinalComposition` is the restriction compositor fixed as the identity on
    selected sections; its `.derived` is its exact localization.
    `cofinalExtensionComposition` is constructed from the composed extension
    adjunction and that restriction compositor by left-adjoint uniqueness.
    The main theorem's first conjunct states the h composition equation
    under these maps; its last conjunct is the rho composition equation
    for every pair of subsequences and every third fixed support adjunction.
    No arbitrary compositor replaces the canonical adjunction identifications.
12. Resolution independence is expressed by the actual derived-category
    objects, their universal cochain comparison equations and the canonical
    adjunction construction of rho. The statements quantify over arbitrary
    derived objects and maps, not over a chosen collection of resolutions.
13. `etaleSystemCofinalMate_localField` has E finite dimensional over Q_l,
    O_E defined by the recorded coefficient extension construction, an
    arbitrary uniformizer v specified by `(v)=m_E`, e≥1, and `(s)=(v)^e`.
    `cofinalQuotientTower` is the concrete quotient tower and its quotient
    transition maps. The theorem identifies the whole reindexed v-power
    functor with the s-power functor, and heterogeneously identifies every
    quotient projection from O_E. It also supplies their finite l-primary
    `Coefficients` objects and equality of the selected object with the
    s-power object. This is the canonical identity-on-representatives
    identification, including all transition maps, not an abstract ring
    isomorphism. Dependent substitution along equality of the actual
    coefficient objects transports the strict systems, units, q, h, and
    rho with their map action and the same compactification. Thus the full
    general theorem applies to precisely the local-field specialization in
    the node, including its maps.

### Dependencies used

The signatures and docstrings of the recorded dependencies were read before
writing the statement. No dependency is replaced by a second definition.

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- The convention node `def-weil-scheme-morphism-properties` has no declaration:
  its stipulated Mathlib notions `AlgebraicGeometry.LocallyOfFiniteType`,
  `QuasiCompact`, `IsSeparated` are used directly.
- `WeilConjectures.Compactification.RefinementCategory`: the imported
  `AlgebraicGeometry.Compactification` and its open/proper factorization;
  refinements are not needed for the fixed-compactification assertion.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`:
  `SheafOfModules.systemLevelLeftExtensionTheory`,
  `SystemLevelLeftExtensionTheory`, `SystemDerivedLeftExtension`,
  `systemNextSelected` and its least-index specification, reexported from
  its basic and scalar-model modules. The site universes are explicitly
  objects u+1, morphisms u, modules u+1.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections` and its
  public sequence-site `Systems`, ring objects, derived categories and
  geometric interpretation. The two encodings are connected explicitly by
  identity-on-sections `CofinalEncoding`.
- `Sheaf.Paper.EtaleSystemCoefficientProjection`:
  `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`,
  with its public `Coefficients`, `Theory`, `Support`, `Scalar`, `Evaluation`,
  `SupportEvaluation`, actual q, and ordinary geometry; the existing
  `AlgebraicGeometry.Etale.scalarExtension`,
  `scalarExtensionRepresentative`, and `compactScalarMap` are reused.
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`: its publicly
  retained `SheafOfModules.DerivedChangeOfRingsCochainModel` interface,
  underlying the normalized scalar extensions and K-flat computations.
  The ModuleCat specialization is not substituted for the ringed-site API.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its publicly retained
  `coefficientExtensionIntegers`, `coefficientExtensionMaximalIdeal`,
  uniformizer and quotient constructions. The arbitrary uniformizer in the
  node is retained; it is not fixed to the chosen one.
- Proof imports retain `Sheaf.CategoryTheory.SystemEvaluationKFlat`,
  `SystemSelectedDerivedExtension`, `SystemOrdinarySelectedExtension`,
  `Sheaf.Paper.SystemBlockRepetition`,
  `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages`, and
  `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`.
  In particular `systemNextSelected_monotone` and `blockDerivedComparison`
  are used by the real constructions, and `Padic.local_field_coefficient_stages`
  supplies the local-field finite/torsion proof plan.
- Mathlib `CategoryTheory.Adjunction.comp`, `leftAdjointUniq`,
  `rightAdjointUniq`, `ofNatIsoLeft`, `ofNatIsoRight`, and the exact-derived
  functor composition comparisons are used as constructions.

### Edge cases checked

The zero coefficient ring is permitted. No nontriviality, common annihilating
exponent, surjectivity or flatness of coefficient transitions is assumed.
Empty schemes and zero complexes remain permitted. The first positive level
is Lean zero; no level-zero quotient ring is inadvertently substituted.
The identity subsequence and subsequences skipping initial levels are allowed.
The least-index function can be constant on a block; the dependency's identity
selected transition and tensor associators apply there. Every block is finite
and nonempty for a strictly increasing unbounded subsequence. Composition is
`s.trans r` (function r∘s), in the order of restriction and the displayed mate
word. Inputs may be unbounded and noncartesian. Arbitrary derived morphisms,
not merely degree-zero sheaf maps, occur in the Hom and counit clauses.
Y may be nonseparated. In the local-field case e=1 and a unit multiple of v
are allowed, as is every s generating (v)^e; the quotient identification fixes
representatives and hence transition maps. Small etale site object and morphism
universes are kept distinct throughout; no equality between them is imposed.

### Searches

Searches used the prescribed `msearch.py` interface and direct read-only source
searches. None gives the complete geometric cofinal-mate statement already.

- LeanFinder: `Restriction to a cofinal subsequence commutes with the compact
  support right adjoint via derived left extension and adjunction mates`.
  Eight unrelated condensed/compactly-generated adjunction hits; no match.
- LeanSearch: `Cofinal subsequence restriction left extension derived sheaves
  of modules`. Eight general scalar restriction/scheme restriction hits;
  no theorem with this strict-system geometric comparison.
- Loogle: `Adjunction.rightAdjointUniq, Adjunction.comp, conjugateEquiv`.
  No hits (unknown combined identifier query). The individual Mathlib
  construction was then found and read directly.
- Mathlib grep through msearch: `rightAdjointUniq|conjugateEquiv` in
  `CategoryTheory/Adjunction`. Sixteen hits, including uniqueness and mates;
  those give the categorical construction, not the geometric theorem.
- Read-only `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  cofinal restriction/mate and selected-extension names found the already
  recorded general selected-extension, projection and block-repetition
  interfaces. The item id search in upstream found no existing statement.
  Final exact-name searches for `cofinalMate`, `cofinalRestriction`, and
  `etaleSystemCofinal` found no previously landed declaration.

No STATEMENT-DISPUTED issue or node fault was found. The natural-language node
is unchanged. Every definition contains real data, and each postponed proof is
a named theorem with its source and natural-language proof in its docstring.

## Second reading by Q88

No independent second worker is claimed: this dispatcher assignment requires
direct worker delivery, followed by the maintainer's independent review.
The author's final clause-by-clause reading checked the actual system
normalization in addition to evaluation, the ordinary and derived tensor
normalizations, both composition words, arbitrary fixed adjunctions, and the
identity-on-representatives local-field identification.
