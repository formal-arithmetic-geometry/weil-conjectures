## Worker report

The module `Sheaf.AlgebraicGeometry.ProjTwistSectionBasicOpen` states
`AlgebraicGeometry.Proj.twistSectionBasicOpen`, with its sole proof `sorry`.
Its two helper definitions have real data: `twistSectionOnOpen` restricts the existing
canonical morphism and evaluates it on 1; `twistSectionLoci` collects the existing
stalk-defined nonvanishing sets of those sections. They are interfaces for this item's
specified sections and family, not independent constructions of sheaves or restriction.

Hypothesis and conclusion correspondence, with the node and source read together:

- The nonnegatively graded commutative ring is `{A σ : Type u} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]`.
  Its scheme is exactly the existing `Proj 𝒜`. The grading carrier follows the universe
  convention of the upstream twisting sheaf. Every grading can be represented by its
  additive subgroups of A; no restriction on the ring or its cardinality is imposed.
- `d ≥ 1` is `(d : ℕ) (_hd : 0 < d)`.
- The specified largest open `W_d` is `(W : (Proj 𝒜).Opens)` with `_hW` identifying W
  with the union of `basicOpen 𝒜 (a*b)` over homogeneous a,b whose degrees satisfy
  `α = β + d`. This uses exactly the EQUIVALENT characterization explicitly in the
  node and Stacks 01MU, rather than an arbitrary open or only invertibility of O(d).
  All natural degrees β, including zero, occur. Thus neither the maximality nor the
  all-integer twist/multiplication condition is weakened: their equivalent object is
  specified by its explicit union. These are characterizations of W in the hypothesis,
  not additional conclusions of this section-locus lemma.
- An open subscheme of W is `(U : (Proj 𝒜).Opens) (_hU : U ≤ W)`, with the canonical
  open immersion `U.ι`. Every open subscheme has this representation up to its canonical
  isomorphism. No quasi-compactness or degree-one-cover hypothesis is added.
- Every homogeneous f in degree nd, n ≥ 1, is quantified by
  `∀ (n : ℕ), 0 < n → ∀ (f : A) (hf : f ∈ 𝒜 (n * d)), ...`.
- O_U(nd) is the actual upstream `(twist 𝒜 (0 + ((n*d : ℕ) : ℤ))).restrict U.ι`.
  The harmless `0 +` is the target degree used by `unitToTwist` itself.
- The section s_f is `twistSectionOnOpen 𝒜 U hf`: restrict the existing morphism
  `unitToTwist hf`, precede it by `restrictUnitIso U.ι |>.inv`, and evaluate on the
  unit section. This is precisely the canonical section restricted to U, with no
  arbitrary choice or hypothesis supplying the section.
- The first conjunct uses `Scheme.Modules.nonvanishingLocus` on that restricted module
  and section. It equals the underlying set of `U.ι ⁻¹ᵁ basicOpen 𝒜 f`, exactly the
  intersection U ∩ D_+(f) viewed inside U.
- The second conjunct is `TopologicalSpace.IsTopologicalBasis (twistSectionLoci 𝒜 d U)`.
  The family is defined using the actual section nonvanishing sets, not merely a
  family of already-known basic opens. Its n ranges over all positive naturals.
  Every positive power of an allowed f is included at its multiplied degree.
- The last conjunct restricts that same family to sets admitting an open representative
  `O : U.toScheme.Opens` with `IsAffineOpen O`. It says these form a topological basis,
  exactly the affine-open basis clause. It does not assert arbitrary U ∩ D_+(f) affine.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `AlgebraicGeometry.Proj`,
  `Proj.basicOpen`, `Proj.basicOpenIsoSpec`, `Proj.awayι_preimage_basicOpen`, and
  `ProjectiveSpectrum.basicOpen`. These realize def-pc-proj and the proof's standard-chart
  intersection dependency. Its Mathlib match is used directly without adding a Lean record.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  the immersion of an open is `U.ι`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules`:
  `AlgebraicGeometry.Proj.twist`. Its canonical-section declaration is in the public
  extension `...Twist.UnitToTwist`, which is imported: `Proj.unitToTwist` and
  `Proj.val_unitToTwist_app_top` (the latter identifies its value with f/1).
  Also read the recorded `Proj.twistPowSection` in `...Twist.TensorObj`: it is only a
  degree-one chart interface and is not substituted for arbitrary homogeneous f.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` (imported publicly through Ample).
  It gives the node's invertibility meaning; W is specified by its equivalent chart union.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf`: `Scheme.Modules.restrictFunctor`,
  `Scheme.Modules.restrictUnitIso`, and `Scheme.Modules.Hom.app` construct the section.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`. Its full source was read through
  `scompile.py --source` because this published module is absent from the older checkout.
- `Sheaf.AlgebraicGeometry.ProjStandardOpenProperties`:
  `AlgebraicGeometry.Proj.standardOpenProperties`, whose positive-degree basis and affine
  charts supply the basis proof plan.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality` was read through
  `scompile.py --source` and publicly imported as the recorded tensor dependency. Its
  public `TensorProductOfUniverses` import retains the sheaf tensor construction. In this
  statement the all-multiplication-isomorphism locus is given by its equivalent union,
  so no replacement multiplication morphism or tensor product is constructed.

Sources checked: `constructions.tex`, the complete statements and proofs of
lemma-where-invertible (correct tag 01MU, confirmed in tags/tags), lemma-principal-open
(01MV), and lemma-ample-on-proj (01MW), especially (5)--(7). The node's extension from W
itself to arbitrary open U follows by restriction. Its family of homogeneous sections
already gives the asserted bases, using positive powers of the standard-open basis.

Edge cases checked before drafting: U empty, W empty, Proj empty, the zero ring, f=0,
nilpotent f, d=1, n=1, homogeneous b of degree zero, and a*b=0. Empty standard opens
are allowed. Nilpotent f gives an empty locus; on an empty scheme a topological basis
may contain only the empty set. All inequalities needed for the power argument are
explicitly positive. No ring nontriviality, finite-generation, Noetherian, field,
quasi-compactness, or cover assumption was inserted. No statement fault or
STATEMENT-DISPUTED flag remains.

Searches made for existing declarations:

- msearch.py leanfinder, query `homogeneous twisting section on Proj nonvanishing on
  invertibility open standard basic open`: 8 hits, including sectionInBasicOpen,
  Proj.awayToSection, StructureSheaf.IsFraction, and Proj.basicOpen. None concerns the
  general twist section on W_d together with the two basis assertions.
- msearch.py loogle, query `"Proj", "twist"`: 0 hits.
- msearch.py grep, query `twist|nonvanishingLocus`, subdirectory
  `AlgebraicGeometry/ProjectiveSpectrum`: 0 hits.
- msearch.py leansearch, query `homogeneous twist section nonvanishing locus on Proj
  invertibility locus and affine basis`: 8 hits concerning homogeneous vanishing ideals,
  structure-sheaf charts, and Proj.awayι_preimage_basicOpen; no twist theorem.
- rg of the upstream ProjectiveSpectrum source and project Lean found twist,
  unitToTwist, twistPowSection, and the degree-one-cover theorem
  Proj.compl_support_zeroLocus_unitToTwist. Read its signature and docstring: it treats
  O(1) when degree-one standard opens cover all of Proj, not this arbitrary W_d result.
- rg of DAG statements for `invertibility locus`, `largest open.*twist`, and `W_d`
  found this item and its common-degree consumer; there is no already-defined W_d
  interface. Here W is specified by its explicit union as a hypothesis, so no new
  independent notion/node is introduced. The two helper functions concern precisely
  the section and family in the item. Exact-name searches of Mathlib, upstream, and
  lean/Sheaf found no pre-existing twistSectionOnOpen, twistSectionLoci, or
  twistSectionBasicOpen. Upstream exact-id search found no matching declaration.

## Returned delivery repaired

The returned immutable head ef22da3ea026 was inspected on the server. It was a stage-1
split containing only DAG JSON and a report, without a Lean module. Its proposed
lem-trf-proj-twist-chart-generator was an unsplit statement helper. Current main has
already replaced that split by four explicit proof steps, eliminating the helper as an
elementary chart calculation; its natural-language item statement is unchanged.
The supplied sandbox had only dispatcher marker files, so the packet was reconstructed
from the current main node and the inspected returned report. The obsolete helper and
stage-1 metadata changes are not carried into this stage-2 repair.

The return rejected a full report path passed to the stage-2 `--apply-fixes` parser.
This repair supplies the actual stage-2 module, its node Lean record, and the worker
report through deliver2.py's normal packet layout. It is a substantive new statement
packet, not a rebase or an unchanged re-push. Only the item's `lean` field changes;
there are no new nodes, dependency-node edits, or statement corrections. The local
report is `report.md`; the wrapper owns its final coord/reports/NH path.

## Validation

`scompile.py NH lem-trf-proj-twist-section-basic-open` passed for the delivered module
both as a sandbox file and under its named library module. No errors or warnings were
reported. The first draft's indexed-supremum parser error was repaired by separating
its two typed binders. All Lean lines are at most 100 characters. Comparing the
sandbox JSON with the current shared node shows precisely one changed field, `lean`.
The returned head's mathematical statement was also compared with current main and
is identical. The required `deliver2.py --no-push` preflight follows this compile.

The dry run completed successfully: `deliver2.py NH lem-trf-proj-twist-section-basic-open
--no-push` printed `OK (dry run): commit 868307795e passes the preflight and compiles;
nothing pushed`. Its staged set was exactly the module, the item's node JSON, and the
report. No repair findings remained.

## Second reading by NH

Independent maintainer reading, 2026-10-18, of immutable delivery
1784850be3f4db45b23b1dfd144ee0cade823e0a. This entry is supplied by the independent
maintainer reviewer, not attributed to an additional NH worker. The original disclaimer
was not a reading (delivery-errors H11). This replacement records the completed reading;
no Lean or node change is needed.

Hypotheses and conclusions checked against the node and source:

- The binders `{A σ : Type u}`, the commutative-ring, additive-subgroup and graded-ring
  instances, and `𝒜 : ℕ → σ` give an arbitrary nonnegatively graded commutative ring.
  `Proj 𝒜` is the dependency's actual scheme. The same universe for A and the grading
  carrier follows the upstream twist interface and loses no graded ring: the grading
  can always be represented by `AddSubgroup A : Type u`. No field, nontriviality,
  Noetherian, finite-generation, or degree-one generation hypothesis occurs.
- `d : ℕ` and `_hd : 0 < d` say exactly d ≥ 1. `_hW` identifies W with the full union
  of `basicOpen 𝒜 (a*b)` for homogeneous a,b of degrees α = β+d; β=0 is included.
  This is precisely the equivalent specification of the largest locus in the node,
  confirmed by Stacks 01MU. It is not a hypothesis choosing an arbitrary invertible
  twist. No separate new W_d definition or prerequisite is needed to state this equality.
- `U : (Proj 𝒜).Opens` and `_hU : U ≤ W` give the open subscheme in question. Its
  canonical immersion is `U.ι`; arbitrary presentations of an open subscheme transport
  along its canonical isomorphism to this representation. There is no compactness binder.
- The first conjunct quantifies over every n>0 and every homogeneous f of degree n*d.
  `twist 𝒜 (0 + ((n*d : ℕ) : ℤ))` is the existing O(nd), and restriction is the existing
  `Scheme.Modules.restrictFunctor`. `twistSectionOnOpen` composes the inverse restriction
  unit isomorphism with the restriction of `unitToTwist hf`, then evaluates at 1. Reading
  `unitToTwist` and `val_unitToTwist_app_top` confirms the canonical f/1 section. The
  `0 +` agrees with the upstream target degree and does not alter the twist.
- `Scheme.Modules.nonvanishingLocus` is the dependency's actual germ-outside-maximal-
  ideal-times-stalk predicate. Its equality with the set underlying
  `U.ι ⁻¹ᵁ basicOpen 𝒜 f` is exactly U_s = U ∩ D_+(f), expressed inside U.
- `twistSectionLoci` collects those actual section loci, with every n>0 and homogeneous
  f, rather than replacing them with a family of standard opens. Its positive powers
  occur at the corresponding multiplied positive degree. The second conjunct asserts
  this family's topological-basis property.
- The third conjunct retains precisely the family members having an open representative
  with `IsAffineOpen`. It asserts the affine-open basis, without the false assertion
  that every intersection U ∩ D_+(f) must be affine. All three conclusions match.

The two new helper definitions contain real data and merely expose this item's section
and its family. The sole new theorem has proof `by sorry`. The module and all three
public declarations have source/blueprint docstrings; the theorem's docstring follows
all four DAG proof steps. All variables and the universe are bound, every Lean line is
at most 91 characters, and `lean.statement` is character-for-character the theorem
signature before `:= by`.

Dependencies and sources read: all seven statement-dependency node statements and
records in the snapshot; Mathlib ProjectiveSpectrum.Basic (`Proj.basicOpen`,
`basicOpenIsoSpec`, `isAffineOpen_basicOpen`, `awayι_preimage_basicOpen`), OpenImmersion
(`IsOpenImmersion`), and Modules.Sheaf (`restrictFunctor`, `restrictUnitIso`, `Hom.app`);
upstream Twist.Modules (`twist`), Twist.UnitToTwist (`unitToTwist` and its fraction-value
lemma), Twist.TensorObj (`twistPowSection`), and Modules.Invertible (`IsInvertible`);
the NH side-tree Ample module (`nonvanishingLocus`, `IsAmple`),
ProjStandardOpenProperties (`standardOpenProperties`), and SiteTensorFunctoriality
with its TensorProductOfUniverses public interface. These are existing constructions,
not replacement copies. No dependency repair is required. The tensor import preserves
the recorded interface; the equivalent union hypothesis makes explicit tensor maps
unnecessary in this statement. The basic-open intersection proof dependency is supplied
by Mathlib's `awayι_preimage_basicOpen`, already available through the imports.

Read Constructions `constructions.tex:1853–1994`: full 01MU, 01MV, 01MW statements and
proofs, and checked tags/tags. The inherited source field's “01MS (lemma-where-invertible)”
is a tag typo: 01MS is lemma-when-invertible, while lemma-where-invertible is 01MU.
The delivered module, proof citations, and this report use the correct 01MU. The node's
source field is inherited and outside this stage-2 change; it does not change the
mathematics or require a statement correction. For 01MW, quasi-compactness is used to
choose d; once d and U⊆W_d are given, the asserted basis needs no quasi-compactness.
The chart coefficient c=b^n*f/a^n and the displayed unit-power identity are correct.
Taking g^d preserves D_+(g), and those whole standard opens contained in U are affine.

Independent searches used `rg` across pinned Mathlib, upstream WeilConjectures and
NH lean/Sheaf for the three new declaration names, twist/nonvanishing combinations,
`lemma-principal-open`, `W_d`, and `invertibility locus`. There is no exact existing
statement or duplicate helper. Read the nearest upstream theorem
`Proj.compl_support_zeroLocus_unitToTwist` in ProjectiveSpace/CoordinateSection.lean: it
requires a degree-one cover and a degree-one section, and is not the arbitrary W_d
statement here. Other hits concern projective-space or projective-line special cases.
The worker's recorded semantic and name searches were also inspected.

Edge cases: empty U, W, or Proj; the zero ring; zero or nilpotent f; empty chart a*b=0;
β=0; d=1 and n=1; arbitrary characteristic; arbitrary non-quasi-compact U. The basis
claims on an empty space and the empty section loci are valid. n=0 and d=0 are excluded
exactly as in the node. There is no silent size restriction on the ring. No pro-etale
substitute or dropped enhancement machinery occurs. Intersecting all statement/proof
dependencies with origin/newtargets-dag:coord/route-pivot-dropped.txt gave the empty
set; no item repair-note path exists at that ref.

Compile reproduced directly from the immutable snapshot using:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NH
lem-trf-proj-twist-section-basic-open
snapshot/lean/Sheaf/AlgebraicGeometry/ProjTwistSectionBasicOpen.lean`.
The installed wrapper currently uses the server side overlay. It returned exit 0:
sandbox `Sheaf/Stage2/Sandbox0.lean` 8.7 s, named library
`Sheaf/AlgebraicGeometry/ProjTwistSectionBasicOpen.lean` 51.8 s, no Lean errors or
warnings. Initial multiplex-session diagnostics did not prevent successful compilation.
The worker's recorded dry-run success was read; no delivery, merge, global build, live
Lean write, or repository mutation was performed in this review.

Finding and correction: H11 only, the original second-reading disclaimer. This complete
report replacement supplies the independent audit. No mathematical mismatch, hollow
definition, arbitrary map, missing clause, or unintended assumption was found.
