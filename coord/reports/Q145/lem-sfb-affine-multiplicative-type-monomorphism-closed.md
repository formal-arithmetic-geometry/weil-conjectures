## Worker report

The module Sheaf.AlgebraicGeometry.AffineMultiplicativeTypeMonomorphismClosed states
AlgebraicGeometry.affine_multiplicativeType_monomorphism_closed, with sorry as its only proof.
No definition or auxiliary theorem is introduced. The source is Conrad, Reductive group
schemes, Appendix B, Definition B.1.1 and Lemma B.1.3, printed pp.280--282:
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf . I opened the source PDF and read
the displayed definition and lemma. The theorem docstring carries all five steps of the
accepted split, including the universal stabilizer quotient and identity-section evaluation.

Clause-by-clause rendering:

- Any scheme S: `{S : Scheme.{u}}`, with u explicit and unrestricted.
- S-group schemes H and G: `H G : Grp (Over S)`. The bundled group objects have
  multiplication, identity and inverse and their diagram identities.
- H commutative: `[IsCommMonObj H.X]`.
- H of finite presentation: `[LocallyOfFinitePresentation H.X.hom]`,
  `[QuasiCompact H.X.hom]`, `[QuasiSeparated H.X.hom]`, following the exact three-part
  convention in def-weil-pbc-scheme-conventions.
- Multiplicative-type splitting: `hH` gives rings `R : I → CommRingCat.{u}`, structural
  maps `p : ∀ i, Spec (R i) ⟶ S`, and groups `M : I → AddCommGrpCat.{u}`.
  `∀ i, AddGroup.FG (M i)` is finite generation, with no torsion-freeness condition.
  `Presieve.ofArrows ... p ∈ Scheme.fppfPrecoverage S` states flatness, local finite
  presentation and joint surjectivity of the family. The final clause of hH is a
  `Nonempty` isomorphism in `Grp (Over (Spec (R i)))` from the actual base-changed H
  to `ringDiagonalizableGroup (R i) (M i)`.
- The original cover permits arbitrary schemes S_i. Replacing it by an affine refinement
  is equivalent: cover each S_i by affine opens, restrict its character group and splitting,
  and compose the fppf covers. Conversely the displayed affine cover is already a cover
  of the original kind. No uniform group or uniform rank is imposed. This formulation
  uses the existing canonical ring construction rather than duplicating relative Spec or
  gluing group algebras. The ring node is already landed and has been added to stmt_deps
  under the rule permitting gained landed nodes; no node statement is changed.
- The split models have precisely the Hopf operations of the node: the existing
  ringDiagonalizableGroup uses AddMonoidAlgebra, its canonical Hopf structure and hopfSpec.
  Its isomorphisms preserve operations, rather than merely underlying schemes.
- G affine: `[IsAffineHom G.X.hom]`, whose definition is affineness of inverse images of
  affine opens, rather than absolute affineness of G.
- G of finite presentation: `[LocallyOfFinitePresentation G.X.hom]`; quasi-compactness
  and quasi-separatedness follow from affineness (an affine morphism is separated).
  Thus the omitted redundant binders do not omit hypotheses of the node.
- j is an S-group homomorphism: `j : H ⟶ G` in the bundled group-object category.
- Injectivity for every S-scheme: `hj : ∀ T : Over S, Function.Injective
  (fun x : T ⟶ H.X ↦ x ≫ j.hom.hom)`. This tests all schemes in the same universe
  as S, H and G, including H and every affine universal quotient test scheme; it is
  categorical monicity and remains so after enlarging the universe. No independent
  lower test universe or only-field-points restriction occurs.
- Conclusion: `IsClosedImmersion j.hom.hom.left`, the underlying scheme morphism.
- Torsion and nonsmoothness: AddCommGrpCat plus AddGroup.FG allows finite cyclic groups;
  no Smooth, reducedness, characteristic or field hypothesis occurs.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom,
  from def-pc-scheme. Read the structure declarations and docstrings.
- Mathlib.AlgebraicGeometry.Sites.Fpqc: Scheme.fppfPrecoverage (and fppfTopology),
  from def-pc-fppf-site; its definition is the jointly surjective precoverage for
  Flat and LocallyOfFinitePresentation. The covering predicate uses the precoverage.
- def-weil-pbc-scheme-conventions is a convention record with no module. Read its full
  statement and record; use Mathlib LocallyOfFinitePresentation, QuasiCompact,
  QuasiSeparated and IsAffineHom, with their source declarations read.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: AlgebraicGeometry.IsClosedImmersion,
  from def-weil-closed-immersion. Read its closed-embedding and surjective-stalk definition.
- Sheaf.AlgebraicGeometry.RingDiagonalizableGroup: AlgebraicGeometry.ringDiagonalizableGroup,
  from def-sfb-ring-diagonalizable-group (the newly cited landed statement dependency).
  Read the full module and the canonical Hopf-spectrum construction.
- Proof imports include AlgebraicSpaceFppfCoveringCalculus and FpqcClosedImmersionDescent,
  and Mathlib's quotient ideal operations. The other Mathlib proof dependencies are
  provided by the statement imports (Fpqc, Scheme and the affine-group import chain).
  lem-sfb-group-algebra-coaction-grading and lem-sfb-graded-stabilizer-strong-products have
  no recorded Lean modules at reading time, so cannot yet be imported. Their names and
  exact role remain in the proof docstring. No import cycle was introduced.

Edge cases checked before writing: S may be empty; the splitting index has no Nonempty
binder and an empty family is allowed exactly on an empty base. Covering members may be
empty, since zero rings are allowed. The trivial group M = 0 and all finite torsion groups
are allowed. The source group can be nonsmooth, for example a roots-of-unity group in
its torsion characteristic. G need not be globally affine, since only its structural
morphism is affine. H and G need not be smooth, reduced, connected, Noetherian, or defined
over a field. Cover groups can vary with i. The index and rings use the scheme universe,
consistent with the project's covering size convention.

Searches actually run with msearch.py (group Q145 and this item):

- leanfinder: "A monomorphism from a group scheme of multiplicative type into an affine
  group scheme is a closed immersion" returned 8 hits on finite/proper monomorphisms
  and closed-immersion APIs. None establishes the multiplicative-type assertion.
- loogle: `"IsClosedImmersion", "Mono"` returned 4 hits: iff_isFinite_and_mono,
  eq_isFinite_inf_mono, iff_isProper_and_mono, eq_proper_inf_monomorphisms. Finiteness
  or properness is not an input here, so these are not an existing match.
- grep: `multiplicative.type|diagonalizable` under Mathlib AlgebraicGeometry returned
  zero hits.
- leansearch: "Group schemes of multiplicative type over an arbitrary scheme split fppf
  locally as spectra of group algebras" returned 8 hits on Scheme, Spec and affine
  schemes, and an unrelated additive-to-multiplicative group equivalence; no match.
- Direct rg searches in lean/WeilConjectures and lean/Sheaf checked the item id,
  MultiplicativeType, multiplicativeType, multiplicative.type, and diagonalizable.
  No existing theorem matches. RelativeTorusMonomorphismClosed treats tori with smoothness
  and a different target condition; ToriMultiplicativeType is field-specific.
  RingDiagonalizableGroup supplies exactly the split ring model and is reused.

Validation: scompile.py Q145 with the delivered file succeeded in sandbox and library
modes (1.6 s and 4.7 s respectively), with no errors or unexpected warnings.
There is no STATEMENT-DISPUTED flag, node fault, new node or dependency repair.

## Second reading by Q145

This is a second self-reading, not an independent reviewer: the dispatcher explicitly
forbids starting other agents; the maintainer supplies the independent review.
Reopened the node and completed module and compared each binder and conclusion above.
The affine-cover refinement is equivalent to the stated arbitrary fppf cover and retains
its group isomorphisms. The target remains relatively affine, and the character groups
remain arbitrary finitely generated abelian groups, allowing torsion. The pointwise
hypothesis ranges over Over S, not just fields or affine spaces. Finite presentation has
all three conventional components, with the affine target's two redundant components
inferred. The conclusion is closed immersion of j itself. No mismatch required a node
correction; the only dependency gain is the already existing ring-diagonalizable node.
