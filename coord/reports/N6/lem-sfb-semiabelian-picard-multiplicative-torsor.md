## Worker report

The module `Sheaf.AlgebraicGeometry.SemiabelianPicardMultiplicativeTorsor` states
`AlgebraicGeometry.semiabelian_picard_multiplicative_torsor`. Its only theorem has
proof `sorry`; it introduces no definitions or chosen schemes. The node's statement,
proof and proof dependencies are unchanged. Four already landed definition nodes are
added to stmt_deps to own the notions already present in the prose.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`. `H : Grp (Over (Spec (.of k)))` and
  `[IsCommMonObj H.X]` supply its given commutative group law over k.
- Smoothness is `[Smooth H.X.hom]`. Separatedness is precisely the requested closed
  diagonal, `[IsClosedImmersion (pullback.diagonal H.X.hom)]`. Finite type is
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- The fixed algebraic closure is Mathlib's `AlgebraicClosure k`. The geometric group
  is `(MultiplicativeType.baseChange (K := AlgebraicClosure k)).obj H`, using the
  actual pullback of group schemes. The rank is `r : ℕ`, including zero.
- The geometric abelian quotient is `A : Grp (Over (Spec (.of (AlgebraicClosure k))))`,
  with `[IsCommMonObj A.X] [IsProper A.X.hom] [Smooth A.X.hom]` and
  `[GeometricallyConnected A.X.hom]`. No additional dimension or projectivity is assumed.
- The group arrows `i` and `q` have exactly the displayed geometric source and
  target. `hkernel : IsPullback ...` says the entire kernel, including its inclusion,
  is the split torus. `hlocallySurjective` is fppf-local surjectivity of q on every
  test scheme. These give the exact sequence of fppf sheaves, not surjectivity merely
  on field-valued points.
- `T : H.X.left.Modules` and `[T.IsInvertible]` are the given invertible module.
  `halgebraicallyTrivial` applies the already defined `AreAlgebraicallyEquivalent`
  to the tensor inverse image of T along `pullback.fst` and the structure sheaf of
  the geometric group. The dependency's `LineAlgebraicEquivalenceStep` uses exactly
  pairs of fibres of smooth connected finite-type variety families and isomorphisms;
  `Relation.EqvGen` takes chains on isomorphism classes.
- `u : unit (𝟙_ ...).left ≅ (tensorPullback η[H.X].left).obj T` is a frame of e*T.
  Over Spec k an isomorphism O to this line is exactly a nonzero vector in the
  one-dimensional fibre. This avoids selecting a basis or coordinates for that line.
- The conclusion existentially gives `E : Grp ...`, projection `p`, inclusion `j`,
  `F : FrameModel T` and `c : Over.mk p.left ≅ F.space`. Thus E is the representing
  frame scheme over H, up to the unique universal-frame identification. `FrameModel`
  asserts the canonical bijection on every H-scheme by tensor pullback of its universal
  frame; it is not an unconstrained pointwise bijection. Existence is a conclusion,
  not an extra hypothesis or a definition selected from an arbitrary existence axiom.
- `s : Over.mk η[H.X].left ⟶ Over.mk p.left` is the point lying over e.
  `s.left = η[E.X].left` and `F.at (s ≫ c.hom) = u` say its identity is precisely u.
- `IsCommMonObj E.X`, `IsMonHom p` and `IsMonHom j` assert the required commutative
  group law and group homomorphisms over the original k.
- `IsPullback j (toUnit ...) p η[H.X]` identifies G_m with the full kernel.
  `Presheaf.IsLocallySurjective ... (yoneda.map p)` gives fppf epimorphy, completing
  exactness of 1 to G_m to E to H to 1.
- The final universally quantified equation compares frames for arbitrary H-schemes
  U and all x,y over the same H-point, when `y = x * (z ≫ j)`. The frames differ by
  `smulHom` of the pullback of the Laurent coordinate t along z. Thus multiplication
  by j(z) is exactly the stated positive scalar action on frames. In particular,
  apply it at the identity frame u to get j(a)=au, using commutativity. This states
  both the specified embedding and its action, without replacing either by an arbitrary map.
- Every inverse image of a module is the recorded `tensorPullback`; evaluation
  `F.at` uses its normalized composition comparison and canonical unit comparison.
  No perfection, split-torus condition over k, or characteristic condition is added.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.CategoryTheory.Monoidal.Grp` and the group-scheme conventions exported
  by `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `Grp`, `GrpObj`,
  `IsCommMonObj`, `IsMonHom`, and the induced groups on Hom sets.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`:
  `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: actual scheme base
  change via `Over.pullback` and `pullback.fst`; read the recorded module-base-change
  signature and docstring, but do not confuse module base change with scheme base change.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`,
  `.fppfPrecoverage`, `.zariskiPrecoverage_le_fppfPrecoverage`; the slice topology
  and `Presheaf.IsLocallySurjective` use Mathlib's Over/LocallySurjective modules.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: `tensorPullback`,
  `tensorPullbackSectionComp`, and the section-normalized tensor pullback interface.
- `Sheaf.AlgebraicGeometry.LineAlgebraicEquivalence`:
  `Scheme.Modules.AreAlgebraicallyEquivalent`, `LineAlgebraicEquivalenceStep`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.baseChange`, `.splitTorus`.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative`, `.multiplicativeGroup`.
- `Sheaf.AlgebraicGeometry.SplitTorusTorsorFrameGeometry`:
  `SplitTorusFrames.FrameModel`, `.FrameModel.at`, `.pullFrame`, `.unitComparison`.
  These have definition owner `def-sfb-split-torus-frame-model`; no copy is introduced.

Recorded proof dependencies are imported: `SemiabelianGeometricPowerIntegrality`,
`ProjectiveBundleQuotientGeometry`, and the invertible-module and group-scheme
interfaces. Zariski-covers-are-fppf is exported by Fpqc. The nodes
`lem-sfb-semiabelian-picard-square-triviality` and
`lem-sfb-rosenlicht-product-unit-factorization` have no Lean record or Mathlib match
at the time of reading, so there is no module to import for them yet. They are proof
inputs only; no statement prerequisite is missing.

Edge cases checked: r=0 is admitted and `splitTorus` is the trivial group; A or H
may have dimension zero; the trivial group H=Spec k gives the usual G_m of frames
of a one-dimensional vector space with arbitrary identity frame u. T=O is included.
The empty group scheme cannot occur because a group object has an identity over the
nonempty Spec k. Empty test schemes and nonreduced test schemes are included in the
universal frame and scalar equations. There is no field-point surrogate for fppf
surjectivity. AlgebraicClosure k is in Type u, so scalar extension and test schemes
use a single fixed scheme universe without a vacuous independent smaller universe.

Searches (msearch.py, N6 / this item):

- LeanFinder query: "A geometrically algebraically trivial invertible sheaf on a
  semiabelian group scheme has a multiplicative frame torsor which is an extension
  by the multiplicative group". Eight hits: ring Picard functors, sheaf cohomology,
  module sheaves and affine-space Hom equivalences; no exact theorem.
- Loogle query: "GrpObj, IsCommMonObj, Units". Zero hits; remote index reported
  unknown identifier GrpObj. Local source reading supplies the exact group-object API.
- Mathlib grep query: "frameTorsor|FrameTorsor|Semiabelian|AreAlgebraicallyEquivalent".
  Zero hits.
- LeanSearch query: "The frame torsor of an algebraically trivial line bundle on a
  semiabelian variety admits a commutative group scheme extension structure by Gm".
  Eight hits: AddTorsor, abstract GroupExtension and ring Picard groups; no scheme theorem.
- Local rg of `lean/WeilConjectures` and `lean/Sheaf` for semiabelian, frameTorsor,
  FrameTorsor, AlgebraicallyEquivalent, algebraicallyEquivalent and multiplicative
  torsor, and item-id search of WeilConjectures: no existing theorem for this item.
  The searches found the reusable LineAlgebraicEquivalence and SplitTorusFrames
  interfaces, which are imported. DAG search located their already landed owners.
- `tools/blueprint_refs.py search 'frame torsor'`: two divisor/Kummer blueprint nodes,
  neither the current assertion nor another owner of its frame-model interface.

Sources: read Milne AV I 8.4 (printed pp.35--36) and Section 9 (p.41), alongside the
node's seven-step agent-formulated semiabelian proof. Raynaud's named book remains
unavailable locally, as the source field explicitly records; the statement is not
presented as a verbatim theorem from that book. No statement dispute or correction.

Validation: scompile.py compiled the sandbox probe and the actual library module
cleanly (2.0 s and 2.2 s), with no error or non-sorry warning. All variables and
universes are explicit; autoImplicit and relaxedAutoImplicit are disabled.

## Second reading by N6

Reopened the node and compared the final signature clause by clause. The input
sequence is over the algebraic closure only; E and both output arrows are over k.
The geometric line is the actual tensor pullback along the first projection. The
frame at e is a module isomorphism rather than an arbitrary section. The frame model
is asserted to exist, and its representing bijection is canonical pullback, not an
added representation hypothesis. The identity equation is read through c over H;
the kernel square is in the category of k-schemes, with the actual inclusion j.
The final scalar equation uses the Laurent generator and all test schemes, and
specializing at the identity yields j(a)=au. The r=0 case remains present.
No mismatch required a statement correction. This is a final self-check: the
assignment forbids spawning agents; the maintainer's independent delivery review
provides the independent reading, as stated in the brief.
