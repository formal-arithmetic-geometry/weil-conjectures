## Worker report

The module `lean/Sheaf/TraceFormula/FiniteBaseSplitsEtale.lean` states
`AlgebraicGeometry.finite_base_splits_etale` with `sorry` proof. It expands the
node's Noetherian hypothesis as `[IsLocallyNoetherian S] [CompactSpace S]` and
finite presentation of each `u i` as `[LocallyOfFinitePresentation (u i)]`,
`[QuasiCompact (u i)]`, and `[QuasiSeparated (u i)]`. A finite family is
`{I : Type u} [Finite I]` and `U : I → Scheme` with structural maps
`u : ∀ i, U i ⟶ S`.

The conclusion renders the finite surjective morphism as
`∃ (T : Scheme) (r : T ⟶ S), IsFinite r ∧ Surjective r`. For every `i`, it
renders the finite set `J`, schemes `W : J → Scheme`, and maps `w j : W j ⟶ T`
with `IsOpenImmersion (w j) ∧ QuasiCompact (w j)`. The displayed
`Scheme`-theoretic isomorphism is
`e : pullback (u i) r ≅ ∐ W`, and
`e.hom ≫ Sigma.desc w = pullback.snd (u i) r` states that each coproduct
summand maps to `T` by its open immersion. The pullback is the recorded
`def-pc-fibre-product` notion (`CategoryTheory.Limits.pullback`). Empty `I`,
empty `U i`, and empty `J` are represented by `Finite` index types and the
usual empty coproduct cases.

The dependency declarations used are Mathlib's `AlgebraicGeometry.IsLocallyNoetherian`
(module `Mathlib.AlgebraicGeometry.Noetherian`), `CompactSpace` (module
`Mathlib.Topology.Defs.Filter`), `AlgebraicGeometry.IsFinite` (module
`Mathlib.AlgebraicGeometry.Morphisms.Finite`), `AlgebraicGeometry.Surjective`
(module `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`),
`AlgebraicGeometry.IsOpenImmersion` (module
`Mathlib.AlgebraicGeometry.OpenImmersion`), and
`CategoryTheory.Limits.pullback` (module
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`). The finite
presentation and étale classes are Mathlib's `LocallyOfFinitePresentation`
and `Etale`.

Searches made: `msearch.py ... leanfinder` for a finite-surjective base change
splitting separated étale maps returned only generic `IsFinite`, `Etale`, and
separatedness declarations; `msearch.py ... loogle` for étale splitting and
finite/open names returned no splitting theorem; `msearch.py ... grep
'etale.*(split|trivial)|finite.*surjective.*(split|open)' AlgebraicGeometry`
found no hits; and `rg` over `WeilConjectures/` and project `lean/Sheaf` found
only the finite-refinement infrastructure (`FactorsLocallyThrough`), whose
statement is local factorization and does not give the coproduct decomposition.
The existing stage-1 split and reviewed report were read; no existing exact
statement was found.

The file compiles cleanly with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q20 lem-trf-finite-base-splits-etale lean/Sheaf/TraceFormula/FiniteBaseSplitsEtale.lean`.

## Second reading by Q20

Independent maintainer second reading, 2026-10-18, of immutable delivery
4be8b03ebb887855c8f3f32ecde36c04c3d4445e. The reader did not author this delivery.
The original placeholder in this section has been replaced by this reading.

Read the item JSON, all seven statement-dependency records, the module and this
worker report from the immutable snapshot. The snapshot's three delivery files
were checked byte-for-byte against the named commit. The commit changes only the
item's `lean` field, adds its one module, and adds this report.

Source: Orgogozo, author draft of “Modifications et cycles proches sur une base
générale”, Lemma 9.1.3 and proof, printed p. 20 (PDF page index 19), read online.
It asserts finite-surjective splitting of a separated etale morphism between
coherent schemes. The node is its Noetherian, finitely presented finite-family
specialization. No unmentioned field, characteristic, reducedness, excellence,
surjectivity of the input maps, or separatedness of S is needed. Also read the
local Stacks text of More on Morphisms 07RZ, lemma-stratify-flat-fp-qf, and the
definitions listed below.

Hypothesis and conclusion audit:

1. `S : Scheme.{u}`, `[IsLocallyNoetherian S] [CompactSpace S]` render exactly a
   Noetherian base. Read Mathlib Noetherian.lean:57 and :103-138: its every-affine
   definition is equivalent to the affine-cover definition of pqf-def-locnoeth.
   Read Properties 01OV, definition-noetherian and lemma-locally-Noetherian.
   `CompactSpace` imposes no Hausdorff condition (Topology/Defs/Filter.lean:283),
   agreeing with def-weil-pbc-quasi-compact-scheme and Topology 005A/Schemes 01K2.
2. `{I : Type u} [Finite I]`, `U : I → Scheme.{u}`, and the explicitly named
   structural maps quantify over finite families, including the empty family.
   `[Finite I]` does not require a chosen enumeration or decidable equality.
3. `[∀ i, IsSeparated (u i)]` is the closed-diagonal condition
   (Morphisms/Separated.lean:44). `[∀ i, Etale (u i)]` uses Mathlib's affine-local
   etale ring-map condition (Morphisms/Etale.lean:41), the convention's etale notion.
   There is no surjectivity assumption on these maps.
4. The three classes `LocallyOfFinitePresentation`, `QuasiCompact`, and
   `QuasiSeparated` are precisely finite presentation in the recorded convention
   def-weil-pbc-scheme-conventions and Stacks 01TP, definition-finite-presentation.
   Read their class fields in Morphisms/FinitePresentation.lean:45,
   Morphisms/QuasiCompact.lean:43 and Morphisms/QuasiSeparated.lean:50. Redundancy
   with etaleness/separatedness introduces no stronger mathematical assumption.
5. `∃ (T : Scheme.{u}) (r : T ⟶ S), IsFinite r ∧ Surjective r` is a finite
   surjection of schemes. Read the recorded classes in Morphisms/Finite.lean:39
   and Morphisms/UnderlyingMap.lean:59 and Stacks 01WH/01RZ. In particular this is
   finite, not merely integral, proper, or a cover in another topology.
6. `∀ i, ∃ (J : Type u) (_ : Finite J) (W : J → Scheme.{u}) (w : ∀ j, W j ⟶ T)`
   allows a separate finite set of summands for each i after one common r.
   `IsOpenImmersion (w j)` is exactly the recorded open-subscheme notion; read
   AlgebraicGeometry/OpenImmersion.lean:38 and Geometry/RingedSpace/
   OpenImmersion.lean:72-92, against Schemes 01HE/01IO.
7. `QuasiCompact (w j)` gives quasi-compact open schemes: T is finite over the
   Noetherian S, hence Noetherian and compact, so a quasi-compact morphism to T
   has compact source. Conversely an open in Noetherian T has Noetherian source,
   so its immersion is quasi-compact (Noetherian.lean:338). Thus the relative
   formulation is equivalent to the node's absolute one under these hypotheses.
8. `e : pullback (u i) r ≅ ∐ W` uses the recorded fibre-product declaration
   (HasPullback.lean:95, :111, :115, :128). Mathlib's scheme coproduct is the
   disjoint open union (AlgebraicGeometry/Limits.lean, sigmaOpenCover/sigmaMk).
   `e.hom ≫ Sigma.desc w = pullback.snd (u i) r` makes this an isomorphism over T;
   the structure map on each summand is w j, not an arbitrary map.
9. No disjointness or covering condition on the images of the w j is imposed.
   Empty U_i and empty J are allowed; for empty I the identity on S suffices.
   Empty S, nonreduced S, disconnected S, open immersions, and repeated overlapping
   open summands are included. No characteristic or degree restriction occurs.
   Universe u is bound and autoImplicit is false. Finite indexing sets can always
   be represented in Type u (Fin n), so the common universe loses no finite-family
   case; all scheme objects and coproducts live in Scheme.{u}.

Every clause passes. The recorded `lean.statement` was compared by exact string
with the original and replacement signatures; both agree verbatim. No statement
correction, new notion, dependency repair, or citer audit is required.

One-definition audit: independently searched Mathlib/AlgebraicGeometry,
slopmaster2/WeilConjectures, and the read-only Q20 lean/Sheaf tree using finite
surjective splitting, etale splitting, `finite_base_splits_etale`, and
`FactorsLocallyThrough`. Opened EtaleFiniteRefinement/Induction.lean and
FinitePresentation.lean: their output is local factorization through an etale
map, not a splitting of its whole pullback into opens. The project's
FiniteEtaleEtaleLocalSplit concerns an etale-local split, not this finite
surjective base change. No exact existing theorem was found. The item record
also contains the actual LeanSearch, LeanFinder, Loogle and grep search results;
these support the worker's negative search, without introducing another notion.
All statement notions use their recorded Mathlib declarations; no private copies.

Proof-plan audit: the induction is simultaneous over all Noetherian bases, with
bound zero handled separately and no surjectivity hypothesis on the complement.
The graph is both open and closed over the finite schematic closure. Removing it
lowers degree over the dense open; the closed degree loci from 07RZ extend the
bound everywhere. Adding the reduced closed complement of the original image
makes the resulting map surjective and contributes empty pullback of U. Finite
fibre products give the common cover and finite projections preserve the compact
open summands. These are the node's nine steps. The relevant recorded dependency
interfaces were inspected, including the ZMT factorization, schematic closure,
bounded-fibre and closed-stratification statements. Two sources absent in the
older checkouts were read through `scompile.py --source`:
WeilConjectures.AlgebraicGeometry.FiniteFiberDegreeBaseChange and
WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme.

Findings repaired in this replacement delivery:

- H11/H1: the original second-reading section was only a disclaimer, not a reading.
  This section supplies the required actual independent clause audit.
- H8: the original proof docstring was a condensed outline, omitting the explicit
  bound-zero case, graph argument and dependency citations. The replacement module
  gives all nine steps, retaining the source and blueprint docstrings.
- H9 / brief-stage2 §3: added ordinary imports for the seven recorded non-Mathlib
  proof-dependency modules. These are the future proof plan, not public statement
  prerequisites. No signature, hypothesis, conclusion or DAG edge changes.

There is one theorem with proof exactly `by sorry`, and no definition, local proof,
private construction, extra axiom, local instance or notation. The replacement's
maximum line length is 92. No pro-etale substitution or dropped infinity/dg/model
machinery appears. Intersection of the current route-pivot dropped list with
stmt_deps/proof_deps is empty; the current shared ref contains no repair note for
this item, so the pre-pivot comparison condition does not apply.

Compiler evidence: the worker recorded the per-file scompile command above.
Independent reproduction on the immutable module returned exit 0, no errors or
warnings: sandbox 12.0 s, library 18.1 s. The replacement with expanded docstring
and proof imports also returned exit 0 without diagnostics: sandbox 4.6 s,
library 22.8 s (temporary Check module name). The final replacement is additionally
compiled at its actual module path under fixes/lean: exit 0, no diagnostics,
sandbox 42.7 s and library 11.3 s. Only the authorized per-file wrapper was used; its current
implementation invokes the server overlay/compiler. No lake/global build, direct
SSH command, live Lean write, project edit, claim, delivery or merge was performed.

Verdict: FIX. The complete replacement module and this complete replacement report
are supplied in merge_delivery.py --stage 2 accepted paths. Mathematics and the
item's statement record remain unchanged.
