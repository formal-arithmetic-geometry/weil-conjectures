## Worker report

The module `Sheaf.Algebra.Homology.TotalOplaxConjugationConstraints` states
`CategoryTheory.TotalOplaxConjugation.constraints`, with its entire proof `sorry`.
Its helpers are explicit composites of the specified isomorphisms and named
propositions collecting the lengthy clauses. There is no choice of a comparison,
no postponed construction, no new independent notion, and no node correction.
The node JSON changes only in `lean`.

Hypotheses and objects, read against the node:

- The four categories are `A₀,A₁,B₀,B₁`, with independently declared object and
  morphism universes, `Category`, `Abelian`, `MonoidalCategory`, and
  `MonoidalPreadditive`. No symmetry is imposed.
- Their colimits are `HasColimitsOfSize.{w,w}` for a common chosen universe, and
  the full tensor-preservation assumptions are the eight quantified
  `PreservesColimitsOfSize.{w,w}` instances. The explicit universe-zero
  restrictions used by the complex API are redundant consequences of these
  hypotheses, by `hasColimitsOfSizeOfUnivLE` and
  `preservesSmallestColimits_of_preservesColimits`; supplying them explicitly
  avoids making an instance choice inside a statement. The same comparison
  formula works in any containing universe; no category universes are equated.
- `E₀,E₁` are functors with `IsEquivalence`, `Additive`, and `Monoidal` instances.
  This is the functor part of the specified strong monoidal equivalences; their
  inverses are not used to choose any new tensor comparison.
- `Fi,Fs` are additive strong monoidal functors. `hFi,hFs` express preservation of
  every coproduct indexed by a countable `I : Type`. The only indices used are
  integer pairs or triples with a fixed degree, all countable. Larger-universe
  countable index sets can be shrunk; no finite-support restriction is imposed.
- `a : Fi ⋙ E₁ ≅ E₀ ⋙ Fs` has exactly the direction in the node. It carries no
  `IsMonoidal` assumption. `complexSquare` is `NatIso.mapHomologicalComplex a`.
- All complexes are `CochainComplex _ ℤ`. Their tensor and constraints are the
  existing signed total tensor and `HomologicalComplex.monoidalCategory`.
  `ιTensorObj` is its actual summand injection. `leftInclusion` and
  `rightInclusion` are wrappers of the existing nested summand injections, not
  new totalizations. `leftUnitInclusion` and `rightUnitInclusion` normalize the
  degree-zero unit component by `singleObjXSelf`.

Constructions and conclusions, clause by clause:

- `tensorComparison` is the displayed ordinary tilde-gamma: first
  `Fs.mapIso (μIso E₀)`, then `a.symm`, `E₁.mapIso (μIso Fi).symm`,
  `(μIso E₁).symm`, and `tensorIso (a.app M) (a.app N)`. Lean's `≪≫`
  reads left to right, reversing the node's typographical order of composition.
- `unitComparison` is precisely tilde-epsilon, with `εIso E₀` forward and the
  other three factors reversed. `hatTensor` and `hatUnit` reinsert the source
  equivalence's inverse tensorator and oplax unit, giving the node's `g,e`.
- `totalTensor`, `totalUnit`, `totalHatTensor`, and `totalHatUnit` use those same
  composites on termwise functors. Their monoidal structures come from
  `mapCochainComplexMonoidal`, whose tensorator is
  `mapCochainComplexμIso` and unit is `mapCochainComplexεIso`. Thus these are the
  specified preserved-coproduct comparisons, rather than arbitrary isomorphisms.
- `InverseAndUnit` first gives the inverse restriction: target injection followed
  by `A.inv.f n` equals tilde-gamma inverse followed by `Fs.map` of the source
  injection. It then gives both chain-level inverse identities and the inverse
  chain equation for every pair of degrees. The signed differential is the one
  in the actual total-tensor complexes, so no sign is suppressed. Finally it
  gives the degree-zero component of J with the necessary `singleObjXSelf`
  transports, and states that its source and target are zero objects in all
  other degrees and its component is the unique map.
- `IntermediateComparisons` gives the A-hat summand formula for arbitrary
  complexes, including when either argument is itself a total. Its second
  conjunct is the ordinary comparison's naturality for arbitrary morphisms,
  including inner summand injections. Together these specify the intermediate
  comparison restrictions in each nested path, before invoking coherence.
  Whiskering uses the existing tensor-of-chain-maps operation, so its restriction
  is exactly the tensor of the indicated component maps.
- `AssociatorPaths` separately states both full path restrictions. The first has
  source associator, outer A-hat, and left-whiskered inner A-hat. The second has
  outer A-hat, right-whiskered inner A-hat, and target associator. Their right-hand
  sides are respectively the node's ordinary first and second paths followed by
  the matching right-nested target injection. Both share `p+q+r=n`.
- `UnitPaths` separately gives the direct and comparison path on the left, then
  those two paths on the right. Their restrictions are `G(λ)`,
  `g ≫ (e ▷ GM) ≫ λ`, `G(ρ)`, and `g ≫ (GM ◁ e) ≫ ρ`, respectively.
- `ZeroUnitSummands` gives vanishing along every map from the left unit total
  when its unit degree is nonzero, and similarly for the right unit total. In
  particular it applies to each specified path; this is the assertion that
  these source summands are zero, rather than a boundedness assumption.
- `SummandDetection` states detection after Fs on every double total, after G
  on every double total, and after G on both nested triple totals. These quantify
  over all degrees and all target objects and maps, so also detect components of
  arbitrary chain maps. There is no truncation or finite-support hypothesis.
- `Recovery` explicitly recovers A by `Fs.mapIso (E₀.mapCochainComplexμIso)`
  followed by A-hat, and J by the analogous epsilon comparison followed by J-hat.
  It also identifies J-hat in degree zero with e. Thus the E₀ comparisons removed
  in the displayed hatted paths are the specified canonical comparisons at every
  occurrence, not the separate tensor comparison of Fs.
- `LiftConstraintEquality` states the three implications from equality of the
  ordinary associator, left-unit, and right-unit paths on all component degrees
  to equality of the corresponding whole chain maps.
- These eight propositions are conjoined in `constraints`. Its docstring carries
  all ten proof steps of the DAG, including inverse cancellation, intermediate
  restrictions, naturality transport without monoidality of a, and detection on
  infinite coproducts. Every definition has real data and its source/docstring.

Dependency declarations read and used:

- Mathlib.CategoryTheory.Abelian.Basic: `CategoryTheory.Abelian`.
- Mathlib.CategoryTheory.Monoidal.Category: `MonoidalCategory`, its tensor,
  associator, and unitors.
- Mathlib.CategoryTheory.Monoidal.Functor: `Functor.CoreMonoidal`,
  `Functor.Monoidal`, `Functor.Monoidal.μIso`, and `Functor.Monoidal.εIso`.
  The latter class is the equivalent interface explicitly permitted by the
  dependency's Mathlib match; there is no duplicate monoidal-functor definition.
- Mathlib.CategoryTheory.Limits.HasLimits: `Cocone`, `IsColimit`, `colimit`,
  `colimit.desc`, and colimit existence classes. Its preservation interface
  renders the small-colimit hypotheses.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: `DerivedCategory` and
  `HasDerivedCategory`, with the complex category underlying this recorded
  dependency. The present node works before localization and requires no
  derived-category existence hypothesis.
- Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso: the recorded
  `PreservesTotalTensorKFlatQuasiIso` / `IsKFlatForTotalTensor` module, which uses
  the same Mathlib binary tensor. No K-flatness premise is introduced.
- WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal:
  the recorded homotopy monoidal structure and underlying
  `HomologicalComplex.monoidalCategory`.
- WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex:
  `mapCochainComplexMonoidal`, `mapCochainComplexμIso`,
  `mapCochainComplexεIso`, the summand and degree-zero component lemmas, and
  their coherence identities. This is the recorded termwise-strong-monoidal
  proof dependency, imported publicly because it also defines the comparisons.
- Mathlib.CategoryTheory.Adjunction.Limits:
  `Adjunction.leftAdjoint_preservesColimits` and
  `isEquivalence_preservesColimits` (the recorded left-adjoint proof dependency).
- `lem-pd-total-oplax-conjugation-summands` has no Lean record or usable Mathlib
  match on the read base. Its statement was read; it is only a proof prerequisite
  for this statement, not a missing object. Its forward formula is described in
  the proof docstring. It supplies no missing definition and does not require a
  second theorem to be stated in this delivery.

Source and edge cases:

Read `sites-cohomology.tex`, lemma-symmetric-monoidal-cat-complexes (Tag 0FPQ):
the degree-zero unit and total tensor constraints are given in its proof hints.
The abstract square and path calculations are the node's agent extraction, not
claimed as a verbatim theorem of Stacks. Read the current blueprint's
`sec-six-functors/sk-thm-sf-verdier-exchange/_section.md` and sketch proof: its
complement retains the tensor-Hom route and this tool does not change it.

Checked degree-zero complexes, negative degrees, unit summands outside degree
zero, zero complexes and zero tensor factors, and unbounded complexes with
infinitely many pairs in each degree. Empty coproducts are covered by tensor
colimit preservation. Identity functors with a nontrivial scalar automorphism a
check the orientation: g has one scalar factor, each associator path has two,
and e has its inverse, so the unitor scalar cancels. The inverse formula has
that scalar inverted. No flatness, exactness, boundedness or monoidality of a is
assumed, and no equality with the preexisting monoidal structure of Fs is stated.

Searches actually run with msearch.py:

- leanfinder: `Conjugating total tensor oplax comparisons by arbitrary natural
  isomorphisms inverse associator unitor restrictions on summands` — eight hits,
  principally ordinary oplax naturality/coherence; no complete statement.
- loogle: `HomologicalComplex, CategoryTheory.Functor.OplaxMonoidal` — no hits.
- grep in Mathlib Algebra/Homology:
  `mapBifunctorAssociator|mapMonoidal|oplax` — six hits, including the existing
  associator and its component lemma; reused these total-tensor notions.
- leansearch: `Inverse conjugated tensor totalization associator unit paths agree
  on summands for arbitrary natural isomorphism of monoidal functor composites`
  — ordinary `coreMonoidalTransport`, inverse tensorator formulas, and functor
  associators; none states the specified total path and summand restrictions.
- rg/grep of WeilConjectures and Sheaf for the item id and
  `TotalOplaxConjugation|total_oplax_conjugation|totalOplaxConjugation` — no match.
  Additional concept search located the existing map-complex monoidal module and
  unrelated ringed equivalence transports, which do not state this functor square.

No STATEMENT-DISPUTED issue or dependency repair was found. The only postponed
proof is `CategoryTheory.TotalOplaxConjugation.constraints`. All checks use
scompile.py; no source library files or launcher scripts were edited.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
