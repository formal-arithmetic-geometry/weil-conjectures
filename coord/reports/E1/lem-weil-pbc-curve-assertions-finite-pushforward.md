## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardAssertions` states
`AlgebraicGeometry.IsCurve.finite_pushforward_assertions`, with proof `sorry`.
There are no new definitions, new nodes, dependency replacements, or statement corrections.
The original node copy changes only its `lean` field.

Source read: Stacks Project Lemma 59.83.5, Tag 0A5D,
https://stacks.math.columbia.edu/tag/0A5D (the local Stacks checkout is absent).
The source says that finite pushforward transfers the eight statements; the DAG's
step-by-step elaboration specifies the separate implications and preservation of torsion.
The declaration docstring carries all eight proof steps and names their supporting nodes.

Hypothesis and clause correspondence:

- Algebraically closed base field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Source separated, finite type, dimension at most one, with torsion abelian F:
  `P : CurveCoefficientPair k`; its fields are `P.C`, `P.toSpec`, `P.isCurve`, `P.F`,
  and `P.isTorsion`. `IsCurve` includes separatedness, locally finite type plus
  quasi-compactness (finite type), and `topologicalKrullDim ≤ 1`.
- Target with the same curve conditions: `{Y : Scheme.{u}}`,
  `g : Y ⟶ Spec (.of k)`, `[IsCurve g]`.
- Finite k-morphism: `f : P.C ⟶ Y`, `[IsFinite f]`,
  `hf : f ≫ g = P.toSpec`. The equality is essential: it makes f a k-morphism.
- Direct image: `G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F` is
  the recorded direct image on abelian sheaves, evaluated on etale objects by base change.
- Part (a): `Y.IsTorsionAbelianSheaf G`. The target scheme already satisfies the
  curve conditions, so this supplies exactly the remaining field of its coefficient pair.
- C1: `VanishingAboveTwo ... FX → VanishingAboveTwo ... FY`; each predicate
  quantifies q with `2 < q` and says its cohomology group is subsingleton.
- C2: `VanishingAboveOneOfIsAffine ... FX → ... FY`; affineness remains inside
  each predicate as a hypothesis and the degree condition is `1 < q`.
- C3: `VanishingAboveOneOfIsPrimaryTorsionSheaf ... FX k → ... FY k`;
  each predicate quantifies a prime p and `[CharP k p]`, assumes p-primary stalks,
  and concludes vanishing for `1 < q`. Positive field characteristic is prime,
  so the prime binder does not exclude any p>0 field characteristic.
- C4: `FiniteOfInvertibleOrder ... FX k → ... FY k`; constructibility and
  torsion of invertible order over Spec k are internal hypotheses, with all q : ℕ.
- C5: `FiniteOfIsProper ... P.toSpec FX → ... g FY`; properness of the
  appropriate structure morphism and constructibility remain internal hypotheses.
- C6: `BaseChangeOfInvertibleOrder ... P.toSpec FX → ... g FY`; prime-to-char
  is an internal hypothesis. All algebraically closed field extensions and cartesian
  squares, and all q : ℕ, are quantified in the recorded predicate. The conclusion
  is bijectivity of the actual cohomology pullback map.
- C7: `BaseChangeOfIsProper ... P.toSpec FX → ... g FY`; the same actual
  pullback maps and field extensions, with properness rather than a torsion-type condition.
- C8: `SurjectiveRestrictionTwo ... FX → ... FY`; the recorded predicate
  quantifies every open immersion and surjectivity of its actual degree-two pullback.
- Final sentence: `Assertions ... P.toSpec FX → Assertions ... g FY` explicitly
  includes the implication between the recorded bundles, in addition to the eight
  separate implications. No source assertion is assumed unconditionally.

The recorded C1-C8 definitions take module sheaves. We use those exact definitions:
`E := (forget₂ (ModuleCat ℤ) AddCommGrpCat).inv ⋙
ModuleCat.restrictScalars ULift.ringEquiv.toRingHom`, and `FX`/`FY` are `sheafCompose`
applied to the original abelian sheaves. The inverse forgetful functor is an equivalence:
every abelian group has its unique canonical ℤ-module structure. Restriction along the
ring equivalence `ULift ℤ ≃+* ℤ` only lifts the coefficient ring to the universe demanded
by the upstream predicates; it adds no coefficients or hypotheses. The composite is
an equivalence preserving limits and colimits, so composing presheaves sends sheaves to
sheaves. Forgetting the resulting modules recovers the original abelian sheaf up to the
counit isomorphism. Consequently its cohomology, its torsion conditions, constructibility
(finite locally constant on a stratification), and actual pullback-map properties are
unchanged. This is reuse of the recorded definitions, not a private copy of any Cj.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the algebraic-closure leaf
  explicitly records this as its algebraically-closed predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`;
  its class has affine inverse images and finite section-ring maps. The integral
  companion in `Morphisms.Integral`, `IsIntegralHom`, was read but is not needed.
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`: `AlgebraicGeometry.CurveCoefficientPair`
  (full structure, including the abelian sheaf and torsion field).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar` (transitively imported by Assertions).
  The node also lists the derived functor, which is not needed to state this item.
- `WeilConjectures.AlgebraicGeometry.Curve.Assertions`:
  `AlgebraicGeometry.IsCurve.VanishingAboveTwo`, `VanishingAboveOneOfIsAffine`,
  `VanishingAboveOneOfIsPrimaryTorsionSheaf`, `FiniteOfInvertibleOrder`,
  `FiniteOfIsProper`, `BaseChangeOfInvertibleOrder`, `BaseChangeOfIsProper`,
  `SurjectiveRestrictionTwo`, `Assertions` and the read `assertions_iff`.
  Full signatures and docstrings were read for each predicate and the bundle.
- Supporting existing tools: `CategoryTheory.sheafCompose`, the inverse forgetful
  equivalence supplied by `Mathlib.Algebra.Category.Grp.ZModuleEquivalence`,
  `ModuleCat.restrictScalars` and its ring-equivalence instance from
  `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, `ULift.ringEquiv` from
  `Mathlib.Algebra.Ring.ULift`. No data is replaced by sorry.

Edge cases checked: empty source and target (the curve class allows Krull dimension ⊥),
zero-dimensional, disconnected and nonreduced curves; zero coefficient sheaf; finite
morphisms that are not surjective; the empty open in C8; degree zero in finiteness and
base change; positive characteristic and characteristic zero; p-primary hypotheses
only in positive characteristic. None is excluded by the binders. Cohomology predicates
use q : ℕ; their negative-degree abelian-sheaf cohomology is zero, so this matches
q≥0 and all q>1 or q>2 of the node. All schemes/fields use the same arbitrary universe
u as the recorded curve and extension predicates; coefficient groups use u+1 to match
the small-etale-site conventions. The ULift is solely for the coefficient-ring universe.

Searches made (real queries are logged in searches.jsonl):

- LeanFinder, `finite pushforward preserves each of eight curve cohomology assertions`:
  eight unrelated Weierstrass-curve map/equation hits; no matching assertion theorem.
- Loogle, `AlgebraicGeometry.IsCurve.Assertions`: unknown identifier on the Mathlib
  service (the predicate is project-specific); no matching theorem.
- LeanSearch, `finite direct image torsion sheaves curve cohomology assertions`:
  service unavailable, Internal Server Error; no verdict inferred from its failure.
- msearch grep, `finite.*[Aa]ssertions|[Aa]ssertions.*finite`: zero Mathlib hits.
- rg in WeilConjectures, `finite.*assertions|assertions.*finite|Assertions.*lowerStar`:
  existing normalization/constant-sheaf reductions are special cases, not this theorem.
- rg and grep -rn of the exact item id in WeilConjectures: zero hits.
- rg in lean/Sheaf and dag/lean_names_upstream.json of the item id and candidate
  `finite_pushforward_assertions`/`assertions_finite_pushforward`: no matching declaration.
- Read upstream Curve/Reductions.lean to confirm that its finite normalization lemma
  only concerns extension-by-zero constant coefficients, not arbitrary F or all separate Cj.
- rg of Mathlib's Grp and ModuleCat sources found the existing equivalence and
  restrictScalars ring-equivalence instances used for the coefficient conversion.

Validation: scompile.py compiled the final 90-line module on the server cleanly,
with no errors or warnings. Temporary #check/example probes were removed. Every
variable and universe is bound explicitly. No statement fault or dispute found.

## Second reading by E1

I read the node statement, its Stacks source (Etale Cohomology, Section 03SB,
Lemma 0A5D), the dependency declarations, and the submitted module independently.
The object and hypothesis correspondence is as follows.

- The algebraically closed field is rendered by `{k : Type u} [Field k]
  [IsAlgClosed k]`; no characteristic assumption is added.
- The source curve and torsion sheaf are rendered by `P : CurveCoefficientPair k`.
  Its fields `P.C`, `P.toSpec`, `P.isCurve`, `P.F`, and `P.isTorsion` give exactly
  the separated finite-type dimension-at-most-one source and torsion abelian sheaf.
- The target is rendered by `{Y : Scheme.{u}}`, `g : Y ⟶ Spec (.of k)`, and
  `[IsCurve g]`, which supplies the target's same curve hypotheses.
- The finite map is `f : P.C ⟶ Y` with `[IsFinite f]`; `hf : f ≫ g = P.toSpec`
  is precisely the assertion that it is a morphism over `k`.
- `G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F` is the dependency
  declaration for the abelian direct image. `Y.IsTorsionAbelianSheaf G` is clause
  (a), and together with `[IsCurve g]` gives the target coefficient pair.
- `FX` and `FY` are the recorded C1--C8 module-sheaf predicates after the canonical
  inverse `Ab ≃ Mod (ULift ℤ)` and restriction along `ULift.ringEquiv`; this changes
  coefficients only by equivalence and adds no hypothesis.
- The conjunction contains, in order, implications for C1, C2, C3, C4, C5, C6,
  C7, and C8, followed by the implication between `IsCurve.Assertions` bundles.
  Their predicates are the recorded definitions, so their quantifiers (degrees,
  affine/primary/constructible/proper hypotheses, extensions and pullback squares,
  and open immersions) are unchanged.

No extra geometric, finiteness, characteristic, or surjectivity hypothesis occurs.
The empty scheme, zero sheaf, zero-dimensional or disconnected curves, nonreduced
curves, non-surjective finite maps, characteristic zero and positive characteristic,
and degree zero are all admitted by the binders. The `p`-primary predicate itself
supplies its prime and characteristic assumptions. Empty opens are admitted by C8.
The shared universe `u` follows the project and dependency declarations and does not
remove any mathematical case covered by the node.

I searched Mathlib, `WeilConjectures/`, and `lean/Sheaf/` with LeanFinder, Loogle,
LeanSearch, `rg`, and `msearch` for finite pushforward preservation of these
assertions and for `finite_pushforward_assertions`. Only the generic `lowerStar`
definition and the unrelated normalization/constant-sheaf special cases were found;
there is no existing declaration of this statement. The searches and their results
are also recorded in `searches.jsonl`.

There was no mismatch to repair. The submitted 90-line module compiled with
`scompile.py` without errors or warnings, and its node `lean.statement` is verbatim
the theorem signature. No new definitions, dependency replacements, or statement
corrections are needed.
