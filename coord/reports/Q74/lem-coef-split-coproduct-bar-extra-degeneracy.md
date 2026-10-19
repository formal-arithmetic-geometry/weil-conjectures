## Worker report

The module `Sheaf.AlgebraicTopology.SplitCoproductBarExtraDegeneracy` states
`FixedObject.SplitCoproductBar.split_coproduct_bar_extra_degeneracy`, with one
`sorry`. The five helpers have real data. `factorCofan` packages the given factor
inclusions into Mathlib's cofan. `initialSection` and `initialInsertion` are actual
coproduct eliminators. `homSetEvaluation` is evaluation on the mapping set, and
`mappingAugmentation` applies it using Mathlib augmented whiskering. No data is
selected from a postponed existence theorem.

The mathematical statement is unchanged. The only added stmt_dep is the landed
`lem-coef-fixed-object-scat-pushout-coproduct`: its fixed-object category/functor
interface is used, not its pushout theorem. This follows brief-stage2 §5,
STMT_DEPS MAY GAIN LANDED NODES. There is no new independent notion or new node.

Hypotheses and clauses, in order:

* `{O : Type u}` is the small object set; `(F A V : Category.{v} O)` are ordinary
  categories on that literal object type. Independent u,v include every small
  category without forcing its object and hom universes to agree.
* `(v : A ⟶ V)` uses `FixedObject.fixedCategory O`. Its homs are ordinary functors
  with identity object map by construction; all categorical arrows here use this
  same category and therefore fix O.
* `(cFV : BinaryCofan F V) (hcFV : IsColimit cFV)` presents the named target F*V
  by its genuine universal property. The word quotient in the node has exactly
  that property: maps act on a word by composing factor images, preserve factor
  relations and are unique. No normal form or freeness is assumed.
* `R : SimplicialObject (Category.{v} O)` uses the Mathlib contravariant ordinal
  convention. `ε : R ⟶ (SimplicialObject.const ...).obj cFV.pt` is its actual
  natural augmentation to that constant target.
* `f`, `a`, and `z` are the F, labelled-A and V factor inclusions. Their types use
  every n : ℕ and every k : Fin(n+1). `hc` asserts that `factorCofan n (f n) (a n)
  (z n)` is a colimit in each degree, so R_n is precisely the coproduct of F,V
  and n+1 labelled copies of A. These are the universal-property data specifying
  the named bar, not extra constraints or a splitting assumption.
* `hfaceF` and `hfaceV` fix F,V under every face. `hfaceA` gives the complete
  formula: in source degree n+1, when k=i=n+1 the image is v followed by z n;
  otherwise k≤i maps to A_k and k>i to A_(k-1), folding exactly the adjacent pair.
  The Fin-bound proofs in that formula exclude the terminal pair only after
  its explicit v case has been handled.
* `hdegeneracyF` and `hdegeneracyV` fix F,V. `hdegeneracyA` sends k≤i to
  `k.castSucc` (the same index) and k>i to `k.succ` (index k+1), leaving precisely
  A_(i+1) unused.
* `haugmentationF` and `haugmentationV` give the two target coprojections;
  `haugmentationA` sends every labelled A through v to the V coprojection, in
  every degree. Together these nine hypotheses are exactly the operator
  definitions in the node. No extra-degeneracy equation is a hypothesis.
* `initialSection cFV hcFV (f 0) (z 0)` is h_{-1}, defined by the binary coproduct
  eliminator, fixing precisely F,V. It has no unconstrained map parameter.
* `initialInsertion R f a z hc n` is h_n. The cofan eliminator sends each
  `.inl k` to `a (n+1) k.succ`, `.inr true` to `f (n+1)` and `.inr false` to
  `z (n+1)`. Thus it inserts the unused A_0, shifts every old label, and fixes F,V.
* The first conclusion says `initialSection ... ≫ ε.app (op ⦋0⦌) = 𝟙 cFV.pt`,
  i.e. epsilon_0 after h_{-1}, in Mathlib diagrammatic order.
* The second says `∀ n, initialInsertion ... n ≫ R.δ 0 = 𝟙 _`, i.e. d_0 h_n = 1.
* The third separately retains `initialInsertion ... 0 ≫ R.δ 1 =
  ε.app (op ⦋0⦌) ≫ initialSection ...`, i.e. d_1 h_0 = h_{-1} epsilon_0.
* The fourth uses `n : ℕ, i : Fin(n+2)` and says
  `initialInsertion ... (n+1) ≫ R.δ i.succ = R.δ i ≫ initialInsertion ... n`.
  Its index range includes the terminal face i=n+1.
* The fifth uses `n : ℕ, i : Fin(n+1)` and says
  `initialInsertion ... n ≫ R.σ i.succ = R.σ i ≫ initialInsertion ... (n+1)`.
* Finally `∀ x y : O, ∃ ed : (mappingAugmentation {left := R, right := cFV.pt,
  hom := ε} x y).ExtraDegeneracy` asserts exactly Mathlib extra-degeneracy data
  for the augmented mapping set. The equalities after this existential fix ed.s'
  and every ed.s n to the homSetEvaluation images of the specified insertions.
  Its degree n is R_n.Hom x y, its augmentation target is cFV.pt.Hom x y, and its
  augmentation maps are the actual restrictions of ε. Thus the conclusion
  concerns those maps, not an arbitrary contraction of an isomorphic object.
* There is no freeness, Kan, nonempty-O, nonempty-hom, faithful-v or injective-v
  hypothesis. No section/homotopy/weak-equivalence consequence is added.

Dependency declarations read and used:

* def-nagata-category: `CategoryTheory.Category` and `CategoryStruct`,
  `Mathlib.CategoryTheory.Category.Basic`, with their full fields and laws.
* def-weil-pbc-simplicial-set: `SSet = SimplicialObject (Type u)` from
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`; the recorded degenerate,
  nonDegenerate, Subcomplex and Finite signatures were also read, although those
  additional clauses are not used by this item.
* lem-coef-extra-degeneracy-contraction:
  `CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy`, `section_`,
  `section_comp_hom` and `homotopy`, `Mathlib.AlgebraicTopology.ExtraDegeneracy`.
  Read the five defining fields: s'_comp_epsilon, s0_comp_delta1, s_comp_delta0,
  s_comp_delta, s_comp_sigma (in the source's Unicode spelling). The conclusion
  uses the structure directly, not the preadditive homotopyEquiv.
* Added landed node lem-coef-fixed-object-scat-pushout-coproduct:
  `Sheaf.AlgebraicTopology.FixedObjectPushoutCoproduct`: FixedObject.Functor,
  Functor.id, Functor.comp and fixedCategory. Read the full local module and
  confirmed its current source with `scompile.py --source`. Its homs have identity
  object function by construction. Its pushout theorem is not used here.
* Mathlib `BinaryCofan.IsColimit.desc`, `Cofan.IsColimit.desc` and
  `SimplicialObject.Augmented.whiskering` are the existing eliminators/transport;
  their source signatures were read. There is no private copy of these notions.

Source checks:

* Opened Dwyer--Kan, *Simplicial localizations of categories*, at the node's URL
  https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/dwyer-kan-1.pdf.
  Read §1.4(ii)--(iv) and the proof of Proposition 8.2, printed p.279 (PDF p.13).
  The paper identifies the row with the coproduct of F, repeated A factors, and
  C, and invokes its contraction; the arbitrary-factor identity calculation here
  is the explicitly identified agent expansion, not a quotation from the paper.
* Read the current main-20261015 ancestor statement and proof at
  `blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint`
  and the historical master ancestor named in proof_origin. This item supplies
  the foundational localization input extracted under that ancestry, and is not
  the unit's own statement.
* The theorem docstring contains all seven DAG proof steps, including the
  contravariant least-index construction, the terminal-face boundary case and
  the mapping-set restriction. No source statement correction is needed.

Edge cases checked before writing:

* Empty O: all fixed-object hom assignments and every conclusion are typed;
  x,y quantification is empty, and the category identities still make sense.
* Empty mapping sets, categories with relations, one-object monoids, identity-only
  categories and a v that collapses nonidentity arrows: the eliminators use only
  functor laws and the universal properties; no letter normal form, nonidentity
  test, injectivity or cancellation is assumed.
* n=0: R_0 has one A factor; h_0 skips the new first A. d_0 folds the shifted
  A_1 into A_0, while d_1 applies v to it. The separate d_1 h_0 identity is retained.
  The fifth family at n=0 includes i=0, and the fourth includes both faces i=0,1.
* In general i=n+1 in the fourth family: both composites send the last old A
  through v into V, and send every other A_k to A_(k+1). This case is not omitted
  by the Fin bounds. Both insertion maps preserve F,V in every degree.
* All variables and both universes are explicitly bound; there are no file-local
  aliases, instances or notations that would change how the signature is read.

Searches made:

* msearch.py leanfinder: “The augmented coproduct bar of categories on a fixed
  object set has an extra degeneracy inserting an unused initial factor”. Eight
  hits, including ExtraDegeneracy, ExtraDegeneracy.const and Cech constructions;
  none states this coproduct-bar assertion.
* msearch.py loogle: `ExtraDegeneracy, Cofan`. No hits; the tool reports
  `unknown identifier 'ExtraDegeneracy'`. This unavailable name query is recorded,
  not treated as evidence of absence.
* msearch.py grep: `coproduct.*bar|bar.*coproduct|structure ExtraDegeneracy`.
  One hit: Mathlib/AlgebraicTopology/ExtraDegeneracy.lean:72, the generic structure.
* msearch.py leansearch: “Extra degeneracy of the augmented coproduct bar of
  categories on a fixed object set by an initial unused factor”. Eight hits,
  all the generic ExtraDegeneracy constructor/recursor/field family. No exact
  coproduct-bar statement.
* rg over `lean/Sheaf`, the upstream WeilConjectures tree, and Mathlib:
  `ExtraDegeneracy|split.*coproduct|CoproductBar|extra.*degeneracy` and
  `coproduct bar|Coproduct bar|split coproduct|extra degeneracy|ExtraDegeneracy`.
  Found the landed FixedObjectBarReordering module. The dry run revealed it is
  now route-pivot dropped; the final module does not import it. Cech,
  partial-sum and free-bar modules concern different constructions.
* `grep -rn 'lem-coef-split-coproduct-bar-extra-degeneracy'` in upstream
  WeilConjectures: no hit. `rg` of upstream declaration index and all source trees
  for the proposed names found no same full declaration name; generic field names
  mappingAugmentation occur only in unrelated namespaces.
* DAG duplicate search for the item, fixed-object bars and initial-factor
  insertion found the item and its reordering sibling/left-properness consumer;
  the sibling's bundle is route-pivot dropped. The final statement is written
  directly with Mathlib simplicial objects, cofans, and operator equalities; it
  introduces no replacement Bar/Operators type.

No STATEMENT-DISPUTED flag and no dependency-interface defect.

## Validation and route-pivot repair

The first representation reused the landed Bar/Operators bundle. Its prescribed
scompile.py run passed both the sandbox check and actual-module-path compilation,
with no errors or warnings. The required delivery dry run then rejected that
bundle: `stmt_deps name route-pivot dropped node(s)
lem-coef-fixed-object-scat-bar-reordering`, and `imports module(s) of route-pivot
dropped nodes: Sheaf.AlgebraicTopology.FixedObjectBarReordering`.

I read `coord/route-pivot-dropped.txt` (human decision 2026-10-18). The assigned
item itself and the bar-reordering sibling are on that list. The fixed-object
pushout/coproduct interface is not dropped, nor are the item's three original
statement dependencies. The final file therefore uses only that permitted
category interface and Mathlib. Its simplicial object, coproduct property and
nine operator equations are written directly; it neither imports the dropped
bundle nor copies its Bar or Operators structures. All five conclusions and
the canonical insertion data retain the original meaning.

## Second reading by Q74

Author's final source-and-signature check, under the dispatcher instruction that
the maintainer supplies the independent reading (no sub-agent was started).
I reopened the node and final module. O,F,A,V,v and the fixed-object functor record
agree. The cofan has exactly F,V and n+1 labelled A factors. Each of the nine
operator hypotheses is one of the node's defining equations. The two eliminators
have the specified restrictions. All five conclusion families have the correct
composition order and Fin ranges, with d_1 h_0 retained separately. The mapping-set
conclusion specifies those exact insertions. No changed mathematical statement or
extra freeness/nonemptiness hypothesis was found. No independent worker review is
claimed; it remains the maintainer's responsibility under this dispatch brief.

The final file, after removing the dropped bundle, passed the prescribed
scompile.py sandbox check and actual-module-path compile with no errors or
warnings. The final node signature matches the file verbatim, all lines are at
most 100 characters, and the only postponed proof is the named main theorem.
