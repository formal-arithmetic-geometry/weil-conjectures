## Worker report

This is the stage-2 statement of the accepted stage-1 split, not another split.
The live queue lists stage 2, and the node has no Lean record. The inherited
stage-1 refusal is addressed by coord/brief-stage2.md §0 (2026-10-22 handoff).
There is no released stage-2 repair note for this item. The sandbox initially
contained only dispatcher brief markers, with no previous Lean packet to reuse.
The delivery changes only the item's lean record, adds one statement module,
and supplies this report. No definitions or helper nodes are needed, and the
sole theorem proof is sorry. No statement correction or dispute is needed.

The statement is AlgebraicGeometry.generic_algebraicity_localized_affine_model
in Sheaf.AlgebraicGeometry.GenericAlgebraicityLocalizedAffineModel.
Every universe and variable is explicitly bound; there are no let/show binders,
private constructions, file-local notations, or extra mathematical assumptions.

### Hypotheses and objects

- Schemes Z and S and morphism g are `{Z S : Scheme.{u}} (g : Z ⟶ S)`.
  The sole finiteness assumption is `[LocallyOfFiniteType g]`.
- The chosen affine opens U = Spec A and V = Spec R are represented by
  `(R A : CommRingCat.{u})`, the open immersions `i : Spec A ⟶ Z` and
  `j : Spec R ⟶ S`, and the two `IsOpenImmersion` instances. This is exactly
  giving affine charts, with no requirement that Z or S itself be affine.
- The chart ring map is `[Algebra R A]`; `hchart` says that its Spec map followed
  by j equals i followed by g. This expresses g(U) ⊆ V and the induced ring map,
  not an arbitrary algebra unrelated to the given morphism.
- The chosen target point s and corresponding prime are encoded together by
  `(p : PrimeSpectrum R)`, with s = j p. An open immersion is an isomorphism
  onto its open image, so every point s in the chart is represented uniquely.
  This parameterization neither restricts s nor requires equality transport
  in every stalk expression. The image of i need not contain a point over s.
- B = R_p is literally `Localization.AtPrime p.asIdeal`, and C is literally
  `A ⊗[R] Localization.AtPrime p.asIdeal`. The tensor's A-algebra map is
  `algebraMap A C`; its B-algebra map is `Algebra.TensorProduct.includeRight`
  converted with `.toRingHom`. No independently chosen C or comparison map.
- The generic algebraicity assumption is `hgeneric`: for every set D belonging
  to `irreducibleComponents Z`, every η with `IsGenericPoint η D`, the field
  algebra induced by `(g.residueFieldMap η).hom.toAlgebra` is
  `Algebra.IsAlgebraic`. That class means that each element is a root of a
  nonzero polynomial, exactly the parenthetical definition in the node.

### Conclusions, in order

1. `(algebraMap R A).FiniteType` states finite type of A over R.
2. `includeRight.toRingHom.FiniteType` states finite type of C over B,
   with the correct right tensor-factor structural map.
3. `IsLocalRing B` and `Ideal.map (algebraMap R B) p.asIdeal =
   IsLocalRing.maximalIdeal B` give localness and m = pB.
4. `IsLocalization (p.asIdeal.primeCompl.map (algebraMap R A)) C` is the
   localization assertion for the actual map a ↦ a ⊗ 1 and the image
   multiplicative set of R minus p. It allows zero in that image.
5. `IsIso ((Spec.stalkIso R p).inv ≫ inv (j.stalkMap p))` refers to the
   canonical map B → O_{S,j p}: first identify B with the stalk of Spec R,
   then use the inverse stalk isomorphism of the open immersion j.
6. `∃ ρ : CommRingCat.of p.asIdeal.ResidueField ≅ S.residueField (j p)`
   and the displayed equality with `IsLocalRing.residue B` specify the residue
   identification induced by that exact stalk map. It is not an untied
   abstract field isomorphism. `p.asIdeal.ResidueField` is definitionally the
   residue field of B, which is B/m.
7. `∃ e : Spec C ≅ pullback (Spec.map (algebraMap R A))
   (Spec.map (algebraMap R B))` gives Spec C ≅ U ×_V Spec B in the chosen
   affine presentations. The two equations for `e.hom ≫ pullback.fst` and
   `e.hom ≫ pullback.snd` fix both canonical projections, using a ↦ a ⊗ 1
   and b ↦ 1 ⊗ b respectively. Replacing the presentations by their open
   images is just transport along the given chart identifications.
8. Quantification over Q' is over `PrimeSpectrum C` with membership in
   `minimalPrimes C`, so it means every prime containing no smaller prime.
9. Q, q₀ and q are bundled prime ideals. The equalities `hQ`, `hq₀`, `hq`
   identify them with the three specified contractions. `hbase` records the
   same q₀ as the contraction of q; it supplies the compatibility needed to
   type the canonical base residue-field map, not an extra assumption.
10. `Q.asIdeal ∈ minimalPrimes A`, `Disjoint` of Q and the denominator image,
    `Ideal.map (algebraMap A C) Q.asIdeal = Q'.asIdeal`,
    `Ideal.map (algebraMap R B) q₀.asIdeal = q.asIdeal`, and `q₀.asIdeal ≤
    p.asIdeal` are respectively minimality, disjointness, Q' = QC,
    q = q₀B, and q₀ ⊆ p.
11. The equivalences α and β are `≃+*` between the required residue fields.
    Each `.toRingHom` is required to equal `Ideal.ResidueField.map` along
    the corresponding localization map. Thus these are the canonical
    equivalences, not arbitrary isomorphisms between the fields.
12. The equality `α.toRingHom.comp (...) = (...).comp β.toRingHom`
    states commutation with the induced residue maps over R → A and B → C.
13. The final `@Algebra.IsAlgebraic ... (...).toAlgebra` is algebraicity of
    κ(q) → κ(Q'), with exactly the canonical B → C residue map.
14. There is no Noetherian, dimension, reducedness, integrality,
    nonempty-source, quasi-compactness, or finiteness-of-components assumption.

### Dependency declarations and source signatures read

Read every stmt_dep node's statement and recorded Lean or mathlib_match, then
read the actual declarations and docstrings in the live source checkout.
All records are usable without dependency repairs:

- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Scheme and Scheme.Hom.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType. Its class is the every-affine-pair
  finite-type condition, with the source/target containment explicitly stated.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Spec and Spec.map.
- def-weil-pbc-localization-at-prime:
  Mathlib.RingTheory.Localization.AtPrime.Basic, Localization.AtPrime;
  Mathlib.RingTheory.LocalRing.ResidueField.Ideal, Ideal.ResidueField.
- def-sc-generic-point: Mathlib.Topology.Sober, IsGenericPoint.
- def-weil-irreducible-components: Mathlib.Topology.Irreducible,
  irreducibleComponents (the dependency has mathlib_match and needs no lean).
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  Scheme.residueField and Scheme.Hom.residueFieldMap.
- def-weil-pbc-finite-type-algebra: Mathlib.RingTheory.FiniteType,
  RingHom.FiniteType; no private finite-generation predicate.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  pullback, pullback.fst and pullback.snd, with Scheme pullbacks supplied by
  Mathlib.AlgebraicGeometry.Pullbacks.

All proof dependencies with stated declarations are also available through the
imports: Mathlib.AlgebraicGeometry.AffineScheme (affine stalk localization),
Mathlib.AlgebraicGeometry.Pullbacks (pullbackSpecIso with both projections),
Mathlib.AlgebraicGeometry.Morphisms.FiniteType (locallyOfFiniteType_iff),
Mathlib.RingTheory.Localization.BaseChange (IsLocalizedModule.rTensor and
map_lTensor), Mathlib.RingTheory.Spectrum.Prime.Topology
(PrimeSpectrum.zeroLocus_minimalPrimes), and
WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
(IsLocalization.prime_localRing_residueField_iso). The last is the upstream
module named by the current record; no retired Sheaf twin is imported.
The seven-step natural-language proof is in the theorem docstring and follows
the accepted node proof without changing it. Read Stacks varieties.tex,
lemma-quasi-finite-in-codim-1, especially the local-base replacement paragraph.
Its later quasi-finiteness assertion needs Noetherian/dimension hypotheses;
this preliminary localization and residue transfer does not use them.

### Edge cases

- Empty Z or empty chart U: A and C can be zero, and both generic-point
  and minimal-prime quantifications can be vacuous. No Nontrivial A instance.
- The localization may kill the chart (the denominator image contains 0).
  `IsLocalization` permits C = 0; the fibre-product statement still identifies
  empty schemes and the minimal-prime clause is vacuous.
- R = 0 has no p, so there is no point s in its affine chart, as expected.
- R a field, p = 0: B identifies with R and C with A; the statement specializes
  to the original chart residue-field assertion.
- Nonreduced A and infinitely many irreducible components are allowed.
  The docstring's single-component closure argument uses no Noetherianity.
- Identity g and arbitrary non-Noetherian R: the residue maps are the
  canonical localization maps, giving the expected isomorphisms.
- All rings/charts live in the common scheme universe u. There is no test
  universe below u that would make a hypothesis vacuous.

### Searches

Actual prescribed msearch.py searches, logged by the wrapper for Q46:

- leanfinder: "Generic algebraicity of residue fields at irreducible component
  points transfers to minimal primes after localizing an affine chart over a
  target prime". Eight hits: integral-scheme genericPoint results, the
  integral-algebra residue-field algebraicity instance, and residue-field
  constructions. None states this multi-clause arbitrary-scheme result.
- loogle: "IsLocalization.minimalPrimes_comap,
  AlgebraicGeometry.pullbackSpecIso". Zero hits for that combined query.
- grep, Mathlib/AlgebraicGeometry: `(generic|algebraic).*(localiz|residueField)|
  (localiz|residueField).*(generic|algebraic)`. Eighteen hits, including
  residueFieldMap, Γ_restrict_isLocalization and integral generic-point tools;
  no combined model theorem.
- leansearch: "Generic algebraic residue field extensions on irreducible
  components persist under localization of affine opens". Eight hits,
  including instIsAlgebraicResidueFieldOfIsIntegral, quotient-residue algebraicity,
  localization constructions and Scheme.residueField. None matches.
- rg of lean/WeilConjectures and lean/Sheaf for the blueprint id,
  localizedAffineModel and generic_algebraicity_localized: no existing match.
  Broader residue-field/algebraicity/localization searches found constituent
  tools only. Checked dag/lean_names_upstream.json as well.

The suggested CompactObject example is currently a withdrawn module with no
remaining declarations; used the same current `module` / public import /
`@[expose] public section` style as live statement modules instead.

### Validation

scompile.py compiled the module as both sandbox and real library module,
with no errors or warnings (10.2 s / 5.5 s on the clean pass). A final pass and
server delivery preflight follow below. No global build or direct Git command
was run, and all authored files are confined to the assigned sandbox.

Final deliver2.py --no-push result: OK, commit fae27491dff passed server
preflight and compiled both sandbox and library module. The packet has exactly
the report, item JSON and one Lean module. The signature record matches the
file verbatim, every line is at most 100 characters, and there is one sorry.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
