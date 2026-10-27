## Worker report

Module: `Sheaf.Algebra.Homology.GoodTruncationStageNaturality`.
Declaration: `DerivedCategory.good_truncation_stage_naturality`.
This is a stage-2 statement with one `sorry`; no definitions or proofs are added.
The node changes only in `lean`. No new nodes, dependency repairs, or statement
corrections are needed.

The index `k : ℕ` denotes the source's positive stage `n = k + 1`.
This parametrizes exactly all positive stages, including n = 1. Composition in
Lean is left-to-right (`≫`), reversing the order of the node's displayed products.

Hypotheses and objects, matched individually:

- The abelian category is `{A : Type u} [Category.{v} A] [Abelian A]`.
  The object, morphism, and localized morphism universes are explicitly bound
  and independent; `[HasDerivedCategory.{w} A]` is the chosen derived localization.
  `CochainComplex A ℤ`, its homology, `DerivedCategory A`, and `Q` are the recorded
  Mathlib notions, including the equivalent localization of the homotopy category.
- `E G : ℕ → CochainComplex A ℤ` are the two stage families.
  `uE k` and `vG k` are the maps from stage k to stage k+1.
- `X Y : CochainComplex A ℤ` are arbitrary ambient complexes.
  `e k : E k ⟶ X` and `g k : G k ⟶ Y` are the augmentations.
- `he` is precisely `uE k ≫ e (k + 1) = e k`;
  `hg` is precisely `vG k ≫ g (k + 1) = g k`.
- `hEvanish` and `hGvanish` are zero cohomology above `(k : ℤ) + 1`,
  using `IsZero ((E k).homology j)` and its G analogue.
- `heiso` and `hgiso` assert the isomorphism of the actual
  `HomologicalComplex.homologyMap` of each augmentation in every degree
  `j ≤ (k : ℤ) + 1`, including arbitrarily negative degrees and the boundary.
- `α : X ⟶ Y` and `hα : QuasiIso α` impose precisely the quasi-isomorphism hypothesis.

Every conclusion, including the specified canonical formulas:

- `truncLE` is Mathlib's good upper truncation: the original terms below the
  cutoff, cycles at the cutoff, and zero above. `ιTruncLE` is its canonical
  inclusion and `truncLEMap` is its induced map on complex morphisms.
- `iX k` and `iY k` are the successive canonical truncation inclusions appearing
  in the two stage identities. They are characterized by
  `iX k ≫ X.ιTruncLE (k+2) = X.ιTruncLE (k+1)` and the Y equation.
  These are not arbitrary chosen maps: `ιTruncLE` is monic, so each factorization
  determines the map uniquely. Existence is already supplied by
  `DerivedCategory.truncation_descends A (k+2)` after arithmetic normalization.
  The existential form exposes that existing notion without a second definition
  or selection of an uncharacterized object. Its componentwise form is exactly
  the inclusion in the node, and naturality follows from the same monicity.
- `cE k` is an isomorphism from `Q.obj ((E k).truncLE (k+1))` to `Q.obj (E k)`;
  its defining hom equality says its forward map is exactly `Q.map (ιTruncLE ...)`.
  `cG` has the analogous equality. Thus the inverse in each displayed source
  formula is actually defined; no invertibility hypothesis has been added.
- `tE k` and `tG k` are isomorphisms with the exact source and target of the node.
  Their hom equalities are literally `(cE k).inv ≫ Q.map (truncLEMap (e k) (k+1))`
  and its G counterpart. Thus the inverses and comparison maps are canonical,
  not merely some isomorphisms between the same objects.
- The first two compatibility equations are
  `Q.map (uE k) ≫ (tE (k+1)).hom = (tE k).hom ≫ Q.map (iX k)` and its G version.
  Coercion of k+1 and addition by 1 has the same integer value as k+2.
- The separate `IsIso (Q.map (truncLEMap α (k+1)))` clause is exactly the
  assertion that the displayed A_n is invertible.
- `a k` is an isomorphism from `Q.obj (E k)` to `Q.obj (G k)`.
  Its hom is exactly `(tE k).hom ≫ Q.map (truncLEMap α (k+1)) ≫ (tG k).inv`,
  the node's conjugation formula in Lean's composition order.
- Its transition equation is
  `Q.map (uE k) ≫ (a (k+1)).hom = (a k).hom ≫ Q.map (vG k)`.
- Its augmentation equation is
  `(a k).hom ≫ Q.map (g k) = Q.map (e k) ≫ Q.map α`.
  This is an equality in the ambient `DerivedCategory A` with the given X and Y.
- The final conjunct expresses bounded above cohomology for all objects in the
  stage comparison: at every k there is an integer b above which the actual
  derived homology objects of QE_k, QG_k, Q(truncLE X (k+1)), and
  Q(truncLE Y (k+1)) vanish. Instantiating at k+1 gives the objects of the next
  stage as well. No bound on QX or QY appears. No termwise bound or resolving
  class is a binder or an implicit premise.

Dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; full class signature/docstring read.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` from `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
  `DerivedCategory.homologyFunctor` and its factorization through Q are from
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `lem-weil-pbc-truncation-descends`: `DerivedCategory.truncation_descends` in
  `Sheaf.CategoryTheory.TruncationDescends`; its whole signature and proof docstring
  were read. Its complex-level preservation of quasi-isomorphisms and its natural
  step inclusion are the stage-3 inputs. No duplicate of that notion was introduced.
- Proof dependency `lem-weil-pbc-truncation-cohomology` is a Mathlib leaf:
  `CochainComplex.quasiIsoAt_ιTruncLE`, with vanishing supplied by the support
  instances in `Mathlib.Algebra.Homology.Embedding.CochainComplex`. This module is
  also imported explicitly as a proof dependency.

Source checked: `literature/stacks-project/derived.tex`, Tag 0794,
`proposition-left-derived-exists`, lines around 9384--9432, including the comparison
square and “The exact same argument shows that these maps are also compatible as n
varies”. The node supplies the expanded inverse-cancellation argument. The module's
docstring records all seven proof steps and names their inputs, retaining the
cohomologically bounded version and the ambient augmentation equality of the node.

Edge cases checked mathematically: k=0 gives n=1; zero complexes give the unique
zero-object isomorphisms; identity alpha still gives the specified conjugation rather
than an arbitrary automorphism. Nonzero cohomology in the cutoff degree is permitted.
Unbounded X and Y are allowed, since neither ambient inclusion is inverted.
E and G may have nonzero terms in arbitrarily high degrees provided their cohomology
vanishes there. Independent category universes and arbitrary chosen localization size
are retained. No statement fault or `STATEMENT-DISPUTED` issue was found.

Searches made before writing (all through the prescribed msearch wrapper plus direct
read-only source searches):

- LeanFinder: “Canonical good truncation derived comparisons for cohomological stage
  models commute with stage transitions and arbitrary augmentations”. Eight hits,
  chiefly `ιTruncLENatTrans`, raw inclusion naturality, and truncation short-complex
  morphisms. No simultaneous canonical stage/augmentation comparison theorem.
- Loogle: `CochainComplex.truncLEMap, CochainComplex.ιTruncLE`. Two hits,
  `CochainComplex.ιTruncLE_naturality` and `_assoc`; these are inputs, not this lemma.
- Grep service: `truncLE.*[Ss]tage|stage.*[Tt]runc|ιTruncLE_naturality`. Five hits:
  raw naturality in Embedding/CochainComplex and uses in DerivedCategory/Fractions.
- LeanSearch: “Canonical isomorphisms between bounded cohomology models and good
  truncations commute with consecutive truncation stages and augmentations”. Eight
  hits, including `ιTruncLE`, natural-index augmentation/truncation, and invertibility
  for strictly bounded complexes; no match for the full conclusion.
- Direct `rg` in Mathlib's Embedding and DerivedCategory sources, the project's
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found raw
  truncation interfaces and the parent `bounded_stage_roof_comparison`, which adds
  a resolving class, termwise bounds, and a functor; it does not state this lemma.
  Searching the item id in WeilConjectures found no matching declaration. Searching
  `goodTruncationStage|good_truncation_stage` found no existing name. The upstream
  `UpperTruncationStepSES` has a private step inclusion and the public existential
  interface already used by `truncation_descends`; it is not redefined here.

Validation: scompile.py compiled the delivered file in sandbox and library module
modes against the published server library, both in 1.5 seconds, without errors or
unexpected warnings. `set_option autoImplicit false` checks explicit binding, and
all lines are at most 100 characters. The only postponed proof is the named theorem.

## Second reading by Q46

The dispatcher brief assigns the independent review to the maintainer and forbids
starting other agents. This section records the author's consistency audit only;
it does not claim an independent worker reviewed the delivery.

Re-read the node alongside the theorem: the ℕ index shift covers exactly n≥1;
he/hg use the stated composition direction; vanishing is cohomological rather than
termwise; heiso/hgiso include degree n; alpha is a quasi-isomorphism; cE/cG pin down
the actual inverses; tE/tG and a have their exact formulas; both t transition
identities and both a identities are present. The final bound excludes the ambient
X/Y, as required. The iX/iY equations uniquely characterize the canonical inclusions,
so their existential packaging weakens none of the equations. No mathematical
mismatch or correction was found. Maintainer's independent delivery review remains
separate from this author audit.
