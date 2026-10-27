## Worker report

The delivery states `SheafOfModules.exactDerivedResolvingIdentification` in
`Sheaf.Paper.ExactDerivedResolvingIdentification`, with one `sorry` and no new definitions.
The node's statement and all its other fields are unchanged. No dependency repair or new
node is required. Sources read: derived.tex, lemma-right-derived-exact-functor (015F),
sites-cohomology.tex, lemma-K-flat-resolution (06YS), lemma-pullback-K-flat (0G7E), and
lemma-derived-base-change (06YY). The resolving normalization and shift refinement are the
agent assembly explicitly described in the node, rather than a claim that 015F itself
states all those clauses.

Hypothesis correspondence:

- The two ringed sites are C, D, JC, JD, R, S. Site object universes uC/uD and morphism
  universes vC/vD are independent; `EssentiallySmall.{r}` expresses smallness relative to
  the common ordinary module universe r. It does not identify site and coefficient sizes.
- `uInv`, `uPush`, `adj`, and `PreservesFiniteLimits uInv` give the geometric morphism.
  `I : AlgebraicInverseImage uInv R RI` specifies the actual transported ring/module
  structures; `c : RI ⟶ S` is the ring homomorphism. It is not assumed flat.
- F is the tensor-formula module pullback: hobj identifies its objects with the existing
  `changeOfRings c (I.modules.obj M)`, and hmap fixes the action on morphisms, including the
  necessary equality transports. Thus F is not an arbitrary exact functor.
- Exactness is `[F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]`, exactly
  the exact-factorization node's convention. The two `HasDerivedCategory.{w}` binders give
  the chosen unbounded derived localizations in a common morphism universe.
- L, epsilon, hL, he give the left derived functor and natural comparison of the recorded
  ringed-topoi-derived-pullback interface. `he` is invertibility on exactly K-flat complexes
  with flat terms. `P.IsKFlatIndependentCoefficients` and the degreewise `IsFlatOnSite`
  hypothesis use the dependency definitions without a copied resolving predicate.
- `[L.CommShift ℤ]` supplies the shifts, and hshift is their resolving normalization:
  epsilon on the shift agrees with shifted epsilon after the source/target shift maps.
  The right side uses the canonical termwise additive functor's shift (identity in each
  degree), exactly as in the exact-factorization node. This is the stipulated normalization
  in the statement, not an added assumption about arbitrary complexes.

Conclusion correspondence, in conjunction order:

1. `∀ M, IsFlatOnSite M → IsFlatOnSite (F.obj M)` is flat preservation.
2. The next quantified P clause preserves both K-flatness and flatness in every degree.
3. `∀ ι : Type r, PreservesColimitsOfShape (Discrete ι) F` preserves every small direct
   sum with its canonical coprojections. This covers the empty family, infinite families,
   and the countable diagonal `{(p,q) : ℤ × ℤ | p+q=n}` used for unbounded total tensors.
4. `F.map (z • v) = z • F.map v` preserves integer multiples on module morphisms.
5. The same equation for `F.mapHomologicalComplex` preserves integer multiples of chain
   maps. These two universal integer-scalar equations include z = -1, every shift sign
   `(-1)^n`, the shifted differential, and all Koszul scalars `(-1)^(pq)` on tensor summands.
   With coproduct preservation they also apply on the full diagonal direct sums. No
   extra tensor-comparison assertion is substituted for the node's sign clause.
6. `∀ A, IsIso (epsilon.app (quotient.obj A))` states invertibility on all complexes.
7. `∃ eta : L ≅ F.mapDerivedCategory` is an actual natural isomorphism of derived
   functors. Its first clause is resolving normalization. Mathlib composition is left to
   right, so `eta.hom.app ... ≫ F.mapDerivedCategoryFactorsh.hom.app ... = epsilon.app ...`
   is exactly kappa_P eta_P = e_P.
8. The eta' clause proves uniqueness from resolving normalization alone; it does not
   demand the all-complex equation of a competing isomorphism.
9. The following A clause is kappa_A eta_A = epsilon_A for every unbounded complex, with
   no flatness, acyclicity, or boundedness restriction on A.
10. `NatTrans.CommShift eta.hom ℤ` asserts the full comparison diagram for every integer.
11. The last M clause specializes the same equation to the actual ℤ-indexed single
   complex `HomologicalComplex.single _ (.up ℤ) 0`. It has no flatness hypothesis on M.
   The target is q_S(F(M[0])); termwise the canonical single-complex comparison identifies
   this with (FM)[0], exactly as the node's final sentence specifies.

Dependencies read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, transparently
  Mathlib `SheafOfModules`. The already published `WeilConjectures.SemilinearSections.Mod`
  is this abbreviation at coefficient universe r and is publicly exposed by the recorded
  derived-pullback module. No new category or abelian instance is chosen.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded sheafified tensor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`,
  Q, Qh, quotientCompQhIso (the Qh/quotient composite is definitionally Q here).
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` (quantifies over all acyclic test
  complexes using the sheafified total tensor).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`,
  exactness of the existing site tensorRight functor.
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`:
  `SheafOfModules.ringedTopoiDerivedPullbackIndependent` and
  `SheafOfModules.RingedPullbackResolutionComparisons`; the theorem takes its L/epsilon
  data and normalization explicitly, so it applies to the canonical functor it provides.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactorsh`, and their
  shift structures. This is the exact-factorization node's Mathlib interface; it has no
  separate project Lean record and none is needed.

Proof-dependency modules are imported without `public`: ModulePullbackPushforwardAdjunction,
Adjunction.Limits, RingedToposFlatPullback, KFlatRingedToposPullback,
KFlatResolutionIndependentCoefficients, Localization.Predicate, and BifunctorShift.
Statement dependencies are public imports. The docstring follows all seven node proof
steps, including uniqueness by resolving replacements and negative-shift compatibility.

Edge cases checked mathematically before writing: identity pullback over ℤ with the
nonflat module ℤ/2 in degree zero; the zero complex; arbitrary unbounded complexes; empty
and infinite coproduct index sets; n = 0, 1, -1 and arbitrary negative shifts; z = 0, -1;
independent site object/morphism sizes; and no flatness assumption on c. None requires a
statement correction or a STATEMENT-DISPUTED flag. The first compiler run caught use of
`CochainComplex.single₀`, which is ℕ-indexed: this was replaced by the ℤ-indexed single
functor. It also required the fully qualified K-flat predicate on a termwise-image term.
The final module compiled in both wrapper modes with no warnings.

Searches actually run through msearch.py:

- LeanFinder: “Exact ringed topos pullback derived resolving normalization unique natural
  isomorphism exact localization commuting integer shifts”: eight hits, including the
  exact-functor shift instances, but no complete representative-normalized theorem.
- Loogle: “Functor.mapDerivedCategoryFactors, NatTrans.CommShift,
  Functor.IsLeftDerivedFunctor”: zero hits with diagnostic unknown identifier
  `Functor.mapDerivedCategoryFactors`; this was not treated as evidence of nonexistence.
- Mathlib grep: `mapDerivedCategoryFactors|map_zsmul` in
  Algebra/Homology/DerivedCategory: ten hits, giving the canonical factorization and uses.
  The source ExactFunctor.lean was then read in full; these are component tools only.
- LeanSearch: “An exact pullback on ringed topoi has a unique natural isomorphism from its
  left derived functor to exact localization normalized on flat term K flat complexes”:
  eight hits, including leftDerivedUnique, leftDerivedNatIso and the localization lift's
  derived property. These generic tools omit flat/resolving preservation, direct sums,
  resolving-only uniqueness, and the specific shift and degree-zero normalizations.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for the node id and resolving-identification
  phrases: no existing complete theorem. Related resolving presentations are specialized
  to tensor constructions, not this assertion. The proposed declaration name was also
  searched in both source directories and dag/lean_names_upstream.json: no collision.

## Second reading by NB

A second pass by the same dispatched worker, not an independent agent: the dispatcher
explicitly forbids starting agents and the maintainer supplies independent review.
I reopened the node and final signature and matched the hypotheses and eleven clauses
above. In particular I checked that the uniqueness predicate for eta' only quantifies over
resolving P, while the all-complex equation is a conclusion; the degree-zero quantifier
has no flatness assumption; the sign quantifier is ℤ, not ℕ; the shift type is ℤ; and the
sites retain four independent universes. The shift normalization uses the unsigned
termwise identity from exact factorization. No source/node discrepancy was found.
Changes from the first draft were the ℤ-indexed single complex, explicit target K-flat
predicate, explicit source/target topology arguments in flatness, and line wrapping.
