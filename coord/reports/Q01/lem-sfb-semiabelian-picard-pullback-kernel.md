## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianPicardPullbackKernel` states
`AlgebraicGeometry.semiabelian_picard_pullback_kernel`, with its sole proof `sorry`.
There are no new definitions, dependency repairs, statement corrections, or disputed
claims. The mathematical statement, accepted proof, and proof dependencies are unchanged.
The source read is Milne, Abelian Varieties, I Propositions 9.2–9.3, printed pp.41–42:
Pic^0 classifies extensions by G_m. The item's statement is the explicitly recorded
character-pushout consequence, not a purported verbatim quotation of Proposition 9.3.
The complete five-step accepted proof is in the theorem docstring, including the character
sign, fpqc descent calculation, and homogeneous-line conclusion.

Hypothesis and conclusion correspondence:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
  Universe `u` is explicit, and both auto-implicit mechanisms are disabled.
- Abelian variety A/F: `A : Grp (Over (Spec (.of F)))` and `[IsAbelianVariety A.X]`.
  `Grp` supplies the specified group law; the recorded abelian-variety class supplies
  properness, smoothness, and connectedness. No extra commutativity assumption on A
  is needed: it is a consequence, as the accepted proof explains.
- Smooth separated commutative finite-type group scheme G/F:
  `G : Grp (Over (Spec (.of F)))`, `[IsCommMonObj G.X]`, `[Smooth G.X.hom]`,
  `[IsSeparated G.X.hom]`, `[LocallyOfFiniteType G.X.hom]`, and
  `[QuasiCompact G.X.hom]`. The last two express finite type exactly as its node
  records it. `IsSeparated` means the diagonal is a closed immersion.
- Nonnegative torus rank: `r : ℕ`, including zero. The actual torus is
  `MultiplicativeType.splitTorus F r`, the finite product of the canonical Laurent
  multiplicative group, with terminal group for the empty product.
- Maps in the group extension: `i : MultiplicativeType.splitTorus F r ⟶ G`
  and `q : G ⟶ A`. Morphisms in `Grp` preserve the given group laws.
- Identification of the torus with the kernel:
  `hkernel : IsPullback i.hom.hom (toUnit (MultiplicativeType.splitTorus F r).X)
  q.hom.hom η[A.X]`. This is the kernel universal property in schemes over F,
  with the bottom arrow the identity section of A. By Yoneda it expresses precisely
  the kernel on all test schemes, and supplies injectivity of i as well.
- Every A-section lifts fppf locally:
  `hepi : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of F)))
  (yoneda.map q.hom.hom)`. The Yoneda map is on `Over (Spec F)`, not the category of
  plain schemes or only rational points. The topology is the recorded big fppf slice.
  No flatness, surjectivity, affine, torsor, or splitting hypothesis is added on q.
- Invertible O_A-module: `N : A.X.left.Modules` and `[N.IsInvertible]`.
- Trivial tensor pullback: `htrivial : Nonempty ((Scheme.Modules.tensorPullback
  q.hom.hom.left).obj N ≅ SheafOfModules.unit G.X.left.ringCatSheaf)`.
  This asks only for the stated isomorphism, with no chosen trivialization or
  compatibility data added to the assumptions.
- Conclusion: `Scheme.Modules.AreAlgebraicallyEquivalent A.X N
  (SheafOfModules.unit A.X.left.ringCatSheaf)`. Reading that actual definition:
  both endpoints are invertible and `Relation.EqvGen` closes isomorphic pairs and
  pairs of fibres from one invertible module on A times_F V. Its V is smooth,
  connected, separated and quasi-compact; smoothness supplies locally finite type,
  so this is exactly the node's smooth connected separated finite-type V.
  Fibres are the recorded tensor pullbacks along two F-rational points. Thus it
  states the equivalence relation on isomorphism classes specified in the node.
  The closing sentence about tensor products and duals describes the group convention;
  the assertion itself does not request a separate construction of the Picard group.

Recorded dependency declarations used and read:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, the algebraically closed clause of
  def-weil-algebraic-closure (no algebraic closure extension is needed here).
- `AlgebraicGeometry.IsAbelianVariety`,
  WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `SheafOfModules.unit`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible and its sheaf imports.
- `AlgebraicGeometry.Scheme.Modules.tensorPullback`, re-exported by the dependency's
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction from the upstream explicit
  tensor construction in WeilConjectures.AlgebraicGeometry.TensorPullback. The
  section-normalized adjunction's signature and source docstring were also read.
- `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback; the same universal
  property is asserted as `CategoryTheory.IsPullback` in the kernel hypothesis.
- `SheafOfModules.cochainModulesMonoidal`, the dependency's recorded
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, publicly imported.
  Existing scheme invertible-module definitions already supply the tensor and dual
  convention. No second tensor construction is introduced.
- `CategoryTheory.GrpObj`, `Grp`, and `IsCommMonObj`,
  Mathlib.CategoryTheory.Monoidal.Grp and Mon: bundled group schemes and their maps.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact;
  `IsSeparated`, Mathlib.AlgebraicGeometry.Morphisms.Separated.
- `AlgebraicGeometry.Scheme.fppfTopology`, Mathlib.AlgebraicGeometry.Sites.Fpqc;
  `GrothendieckTopology.over`, Mathlib.CategoryTheory.Sites.Over;
  `Presheaf.IsLocallySurjective`, Mathlib.CategoryTheory.Sites.LocallySurjective.
- Existing landed notions newly named in stmt_deps:
  def-sfb-tori-multiplicative-type uses `MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType; def-sfb-line-algebraic-equivalence
  uses `Scheme.Modules.AreAlgebraicallyEquivalent`,
  Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence. Their node statements, recorded
  declarations and full definition bodies were read. These additions expose notions
  already present inline in the item's natural-language statement, without changing it.

Every recorded proof module is imported without `public`, except when it is also a
statement dependency (fppf site, invertibility and module pullback). These are the
largest-subtorus module, SmoothFiber, abelian-variety Basic, geometric-power-integrality,
character-pushout, Descent, and HomogeneousLineAlgebraicTriviality. The Mathlib covering
comparison already comes from Sites.Fpqc. The torsor-representability and Rosenlicht
nodes have no usable recorded module yet and remain named in the proof docstring;
they are proof prerequisites, not objects needed to type this statement.

Edge cases checked before writing: rank zero is the terminal group and the kernel
and local-lifting hypotheses force q to be an isomorphism, giving trivial N. If A
is the dimension-zero trivial abelian variety then N is a line over F and is trivial.
For the trivial product extension G = A times G_m^r, a section makes trivial pullback
force N trivial. Nontrivial extensions allow the genuinely nontrivial Pic^0 kernel,
so the conclusion must be algebraic triviality rather than triviality. The structure
sheaf is always an allowed endpoint; the equivalence definition is reflexive and
allows coincident parameter points. There is no positive-dimensional, positive-rank,
characteristic-zero, torsion-order, or chosen-splitting restriction. Empty G and A
are excluded by their identity sections over Spec F, not an added hypothesis.

Searches actually run through msearch.py:

- LeanFinder: “A line bundle on an abelian variety whose pullback to an extension by
  a split torus is trivial is algebraically equivalent to the structure sheaf”.
  Eight hits, including CommRing.relPic, CommRing.Pic.mk_eq_one_iff and the identity
  scheme module pullback isomorphism; none is the extension-kernel assertion.
- Loogle: `"Pic", "pullback"`. Two general category-theory hits on preservation of
  effective epimorphisms and regular-epi categories; no extension-kernel match.
- Mathlib grep (AlgebraicGeometry):
  `algebraicEquiv|AlgebraicallyEquivalent|picard.*kernel|picard.*pullback`.
  No matching theorem.
- LeanSearch: “Line bundle on an abelian variety trivial on an extension by a torus
  is algebraically trivial”. Eight unrelated topological/vector-bundle trivialization
  hits, no match.
- Direct rg in lean/WeilConjectures for the same expression found the curve Picard
  degree-zero kernel and pullback APIs, not this statement; searching the exact node
  id found no declaration there.
- Direct rg in lean/Sheaf found the existing LineAlgebraicEquivalence definition,
  homogeneous-line algebraic-triviality theorem, and citations of this item in
  SemiabelianAbelianQuotientAmpleReflection; none states the present implication.
  ToriMultiplicativeType and StandardGroupSchemes supply the actual split torus.

Validation: scompile.py compiled this single file in both sandbox and library modes
against the published live library, cleanly. deliver2.py --no-push passed server
preflight and compilation (dry-run commit ec17ffef4cc). The final delivery wrapper
repeats those checks before pushing.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
