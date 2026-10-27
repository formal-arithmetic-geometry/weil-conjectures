## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.BorelCharacteristicPicardSequence` states
`AlgebraicGeometry.borel_characteristic_picard_sequence`, with one whole-proof `sorry`.
Its helper instance exposes the existing canonical commutativity of the Laurent Hopf
multiplicative group; it constructs no new group law. No theorem is proved and no data
are postponed. The source was read in Milne, Algebraic Groups (2017), printed p.390
(Theorem 18.15 and its preceding convention) and pp.395--396 (Theorem 18.32 and its
Borel specialization). The current blueprint unit is the six-functor stability proposition;
this lemma is an internal prerequisite, not that unit's statement.

Hypothesis and clause correspondence:

- The algebraically closed field is `(F : Type u) [Field F] [IsAlgClosed F]`.
- The F-group is `G : Grp (Over (Spec (.of F)))`, Mathlib's bundled group object,
  whose underlying scheme and structure map are `G.X.left` and `G.X.hom`.
- Affineness, smoothness and connectedness are `[IsAffine G.X.left]`,
  `[Smooth G.X.hom]`, `[ConnectedSpace G.X.left]`. ConnectedSpace includes nonemptiness.
- Finite type is `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, the recorded
  meaning of def-weil-finite-type-morphism.
- Characters of J are `Additive (J ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`:
  genuine group-scheme homomorphisms, with pointwise multiplication written additively.
  The canonical Mathlib commutative group-object instance is exposed by the helper.
- The derived-series definition of solvability and maximal smooth connected solvable
  closed subgroups are the existing `IsBorelGroupScheme`; its full definition and the
  `GroupSchemeDerivedLength` and `IsDerivedGroupScheme` definitions were read.
- Existence is the first conjunct, `∃ B₀ i₀, IsBorelGroupScheme i₀.hom.hom`.
- Every Borel is covered by the following `∀ B i, IsBorelGroupScheme ... → ...`.
- The represented quotient is the witness `Q : Over (Spec (.of F))`, `q : G.X ⟶ Q`.
  `IsPullback (fst G.X B.X) (fst ... * (snd ... ≫ i.hom.hom)) q q` says exactly
  that the map (g,b) ↦ (g,gb) identifies G×B with G×_Q G. The action is the canonical
  right multiplication, not an arbitrary action. Its identity and associativity are
  already those of the recorded group scheme.
- Zariski local sections are `∀ x : Q.left, ∃ U j s, IsOpenImmersion j.left ∧
  x ∈ Set.range j.left.base ∧ s ≫ q = j`. Together with the torsor square these
  give a locally trivial right B-torsor and represent the sheaf quotient. Surjectivity
  and the quotient universal property follow; no independent arbitrary quotient is used.
- Invertible modules and their Picard classes use `Scheme.Modules.IsInvertible` and
  `Scheme.Pic`. Their tensor product group is the existing `Scheme.Pic.instCommGroup`.
- The characteristic homomorphism is the existential additive homomorphism `c`.
  For every χ, the witness `AssociatedCharacterLineBundle.Presentation G B i Q q χ.toMul`
  specifies the associated bundle with the inverse-character right action, on all test
  schemes, including nonreduced ones. `hP : Scheme.Modules.IsInvertible P.L` and
  `(c χ).toMul = @Scheme.Pic.ofIsInvertible Q.left P.L hP` identify exactly its Picard
  class. The additional presentation data express the canonical associated line bundle,
  not arbitrary descent data or an uncharacterized choice.
- Restriction is `fun χ ↦ Additive.ofMul (i ≫ χ.toMul)`, in the correct composition order.
  `Function.Injective` is the initial zero; `Function.Exact` at the characters of B
  says image restriction = kernel c. `Function.Exact c (Scheme.Pic.mapHom q.left).toAdditive`
  is exactness at Pic(Q); the final `Function.Surjective` is the terminal zero.
- Pullback is the actual existing `Scheme.Pic.mapHom q.left`, whose defining `Pic.map`
  uses the existing invertible-module pullback. No replacement map is quantified.

Recorded dependency interfaces used:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Mathlib.CategoryTheory.Monoidal.Grp / Cartesian.Grp: GrpObj, Grp, group homomorphisms
  and pointwise commutative character group.
- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact / Smooth:
  LocallyOfFiniteType, QuasiCompact, Smooth; Topology.Connected.Basic: ConnectedSpace.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative and multiplicativeGroup,
  the recorded Laurent Hopf group used through the associated-character import.
- Sheaf.AlgebraicGeometry.GroupScheme.Borel: IsBorelGroupScheme, with the scheme-theoretic
  derived series imported from GroupScheme.Semisimple.
- Sheaf.AlgebraicGeometry.GroupScheme.AssociatedCharacterLineBundle: Presentation;
  its whole signature, orbit formula, pullback naturality, and coordinate compatibility read.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible: Scheme.Modules.IsInvertible.
- WeilConjectures.AlgebraicGeometry.PicardFunctor and Picard.Group: Scheme.Pic,
  Scheme.Pic.ofIsInvertible, Scheme.Pic.instCommGroup, Scheme.Pic.mapHom.

The already landed Borel, associated-character, invertible-module, Picard definition,
and Picard group-law nodes were added to stmt_deps under the standing permission to cite
landed notions. There are no new definition nodes, dependency repairs or statement corrections.
The item text and its proof remain unchanged. Plain proof imports include the recorded
homogeneous quotient, split-solvable torsor theorem, affine-dimension dependency, fpqc descent
and proper reduced global-sections module. Three proof nodes have no recorded module yet
(borel-quotient-proper-geometry, rosenlicht-product-unit-factorization, and
smooth-generic-trivial-line-descent), so no nonexistent imports were invented.

Edge cases checked: the trivial group gives the point quotient and zero character/Picard
groups; connected solvable groups have B=G and point quotient; G_a and G_m give their
usual character groups (zero and Z); SL_2 gives the classical characteristic map to Pic(P¹);
PGL_2 retains the nonzero Pic(G) cokernel. Positive characteristic is unrestricted, including
infinitesimal test schemes. No reductivity or commutativity of G is assumed. There is no
extra universe variable on tests: schemes over F use Scheme.{u}, and Picard groups retain
the existing Type (u+1) carrier. No STATEMENT-DISPUTED issue was found.

Searches performed:

- msearch.py leanfinder: "Exact sequence of characters and Picard groups for a Borel subgroup
  quotient of a smooth connected affine algebraic group". Eight hits: ring Picard relative
  exactness and Jacobi--Zariski exactness, none this statement.
- msearch.py loogle: "AlgebraicGeometry.Scheme.Pic, CategoryTheory.Grp, Function.Exact".
  Zero hits; the remote index does not know the project's Scheme.Pic declaration.
- msearch.py grep: "Borel|[Cc]haracter.*[Pp]icard|[Pp]icard.*[Ee]xact" in AlgebraicGeometry.
  Zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf: Borel, borel, characterGroup, CharacterGroup,
  characteristicHom, Picard sequence and the item id. Located the existing Borel,
  associated bundle, character-isogeny sequence, Picard and torsor interfaces. The
  isogeny sequence is a different downstream statement, so it was not reused or imported.
- Read the corresponding definition DAG nodes and their recorded signatures; searched
  the item id in WeilConjectures: no implementation. The only existing occurrence in the
  isogeny module is its proof-plan citation, not a declaration of this statement.

Validation: scompile.py compiled the delivered module separately in both sandbox and
library modes cleanly, with no warnings or errors. Diagnostic #check/#synth probes were
removed. All variables and the universe u are explicitly bound; autoImplicit is false.

## Second reading by Q13

Re-read the node, its source pages, the finished signature and the imported definitions.
The first draft had the restriction composition in the wrong order and left the torsor
action arbitrary. These were corrected before final compilation: restriction is now
`i ≫ χ.toMul`, and the cartesian square uses the explicit (g,b) ↦ gb map. The finished
statement has both Borel existence and the universal assertion for every Borel. Picard
and character groups both use their additive copies. The characteristic-map condition
fixes the sign through the existing presentation, and both middle exactness assertions
and both endpoints are present. Local sections cover every quotient point; the empty
quotient cannot satisfy the torsor square with the nonempty group. No conclusion was
strengthened to properness or regularity, which belong to the proof only. No mathematical
node correction is needed. This is the dispatcher's single-worker rereading; the independent
review is performed by the maintainer on delivery, as the brief specifies.
