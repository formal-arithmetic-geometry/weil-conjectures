## Worker report

The module `Sheaf.AlgebraicGeometry.PicardSpaceCurvesSmooth` states
`AlgebraicGeometry.picard_space_curves_smooth`, with one whole-proof `sorry` and
no new definitions. Only the item's `lean` field changes. The statement and
accepted proof split are unchanged. No new nodes or dependency repairs are needed.

Source read: `literature/stacks-project/quot.tex`, proposition-pic-functor
(Tag 0D2C) and lemma-diagonal-pic (Tag 0D2D); `moduli.tex`,
lemma-pic-functor-qs-lfp (Tag 0DNI) and lemma-pic-functor-curves-smooth
(Tag 0DPK). These give representability, the immersion diagonal,
quasi-separatedness and local finite presentation, and smoothness in relative
dimension at most one. The declaration docstring retains all six proof steps
of the node, including the scalar-inertia calculation and the rank-one argument.

Hypotheses and conclusions, clause by clause:

- Schemes S and C and the specified morphism: `{C S : Scheme.{u}} (f : C ⟶ S)`.
- Proper: `[IsProper f]`. Flat: `[Flat f]`. Finite presentation:
  `[LocallyOfFinitePresentation f]` together with properness. Properness already
  supplies quasi-compactness and separatedness, hence quasi-separatedness;
  additional quasi-compact/quasi-separated hypotheses would be redundant.
- Fibres of dimension at most one: `hdim : ∀ s : S,
  topologicalKrullDim (f.fiber s) ≤ (1 : WithBot ℕ∞)`. Here `fiber` is the
  scheme-theoretic residue-field fibre, and topological Krull dimension is the
  supremum of lengths of chains of irreducible closed subsets.
- The universal structure-sheaf condition: `hO` quantifies over every
  `T : Scheme.{u}` and every `g : T ⟶ S`. The base change is `pullback f g`,
  with structure morphism `pullback.snd f g`. The unit of the canonical tensor
  pullback/pushforward adjunction evaluated at `SheafOfModules.unit
  T.ringCatSheaf` is required to be an isomorphism. Pullback of that unit module
  is canonically the unit on C_T, so this is exactly the specified canonical
  map O_T → (f_T)_*O_C_T. This is the same recorded interface used in
  `picard_diagonal_locally_closed`, not a condition on an arbitrary morphism.
- Representation by a commutative group algebraic space: the existential gives
  `P : AlgebraicSpace S` and `G : (Over S)ᵒᵖ ⥤ CommGrpCat.{u}`, with
  `G ⋙ forget CommGrpCat = P.obj.obj`. Thus G equips precisely the underlying
  sheaf of P with its natural commutative group structure.
- It is the relative Picard sheaf and has the specified group law: the natural
  group isomorphism from `G ⋙ forget₂ CommGrpCat GrpCat ⋙
  GrpCat.uliftFunctor.{u + 1, u}` to `picardFunctorGrp f` identifies it with the
  EXISTING group-valued fppf sheafification. The latter's underlying set
  presheaf is `picardFunctor f` (`picardFunctorGrp_comp_forget`). The original
  `Scheme.Pic` multiplication is tensor product of invertible modules
  (`Scheme.Pic.mul_def` and `mulIso`), and `toPicardFunctorHom` preserves it.
  Consequently this isomorphism identifies the law with tensor product, the
  identity with the trivial bundle, and inversion with dualization. No
  rational section, arbitrary map, or choice of a new Picard sheaf is assumed.
- Smoothness and local finite presentation: for EVERY scheme chart
  `a : yoneda.obj U ⟶ P.obj.obj`, `AlgebraicSpace.IsEtale a` implies
  `Smooth U.hom ∧ LocallyOfFinitePresentation U.hom`, exactly the convention
  stated in the node. No atlas or chart is imposed as an extra hypothesis.
- Quasi-separatedness and immersion of the representable diagonal:
  `AlgebraicSpace.IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left ∧
  IsImmersion p.left) (prod.lift (𝟙 P.obj.obj) (𝟙 P.obj.obj))`. Products in
  presheaves on Over S are relative products over S. `IsRepresentableWith`
  requires an actual scheme representing every test pullback and the indicated
  property of its scheme projection. Thus the diagonal is representable by
  quasi-compact immersions, equivalent to the two requested diagonal clauses.

Dependency declarations read and used (public statement imports):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper` (and its separated
  and universally closed parent classes).
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`, with its stated
  equivalence to flat stalk maps.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  base change uses `Limits.pullback` and `pullback.snd`, as its docstring and
  def-pc-base-change record prescribe, rather than the module-base-change
  functor when a scheme is needed.
- `WeilConjectures.AlgebraicGeometry.Picard.Defs`: `picardFunctor` (the closed
  upstream declaration of sk-def-picard-pic), its unit `toPicardFunctor`, and
  the canonical pushforward-unit description. The normalized functor in the
  same dependency record is used only when a section is specified; none is
  specified or added here.
- `WeilConjectures.AlgebraicGeometry.Picard.Group`: `picardFunctorGrp`,
  `picardFunctorGrp_comp_forget`, `Scheme.Pic.instCommGroup`, and the tensor
  product description `Scheme.Pic.mul_def`/`mulIso`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible`, used by the existing Picard construction.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsRepresentableWith`, `IsAlgebraicSpace`. These take small set-valued sheaves;
  the group-functor isomorphism uses the standard ULift into the u+1 universe
  of the existing Picard construction. It imposes no equality of universes.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`:
  `Scheme.Modules.exists_tensorPullbackAdjunction`, the shared canonical unit
  convention for the structure-sheaf hypothesis.
- Mathlib's existing `Smooth`, `IsImmersion`, `QuasiCompact`, and
  `topologicalKrullDim` render the explicit predicates without new notions.

Proof-only imports include the recorded flat-inertia quotient,
stack-chartwise calculus, space flat/proper/fp locality, Picard pullback locus,
and Mathlib's locally bijective sheafification criterion. The two proof nodes
lem-sfb-picard-stack-curve-geometry and
lem-sfb-space-quasi-compact-immersion-locality have no Lean declaration in the
read snapshot; they remain explicit in the proof docstring and do not enter
the theorem's signature. No statement prerequisite is missing.

Edge cases checked before writing: S empty allows the empty family and its
unique Picard section; there is no nonemptiness binder. An empty fibre over a
nonempty point is excluded by the universal O hypothesis, since its global
functions would be zero rather than the residue field. Fibres of dimension
zero are allowed by `≤ 1`, including the identity family, whose relative
Picard group is trivial. Nodal, reducible and nonreduced fibres are allowed;
no smoothness/integrality of C/S is assumed. Nonreduced test schemes are
included in both hO and diagonal representability. No characteristic,
Noetherian, quasi-compact-base, or rational-section restriction is added.
The anisotropic conic case is covered: the conclusion uses sheafification,
not surjectivity from global line-bundle classes.

Searches actually run on 2026-10-24:

- msearch LeanFinder: “Relative Picard fppf sheaf of proper flat finitely
  presented curves is smooth quasi-separated algebraic space with immersion
  diagonal”. Eight hits, all general scheme smoothness/formal-unramified
  declarations; no relative Picard theorem.
- msearch Loogle: `AlgebraicGeometry.picardFunctor,
  AlgebraicGeometry.AlgebraicSpace`. Zero hits with diagnostic that
  `AlgebraicGeometry.picardFunctor` is unknown to the Mathlib index; this
  cannot establish absence upstream, which was searched separately.
- msearch LeanSearch: “Relative Picard algebraic space of proper flat finitely
  presented family of curves is smooth”. Eight hits, including `CommRing.relPic`
  and scheme smoothness, none stating the node.
- msearch grep: `picardFunctor|Picard.*[Ss]mooth` in Mathlib/AlgebraicGeometry:
  zero hits.
- rg of WeilConjectures and Sheaf for the exact item id: no existing
  declaration; rg for relative Picard smoothness/space names and for
  `picardFunctor`, `CommGroup`, `picardPresheaf`, `toPicardFunctor` found the
  definitions and group-law API used here. Upstream Picard/Scheme.lean is for
  smooth projective curves over a field, so does not state this family result.
- rg across Sheaf for `picard.{0,45}(space|smooth)|smooth.{0,45}picard`
  (case-insensitive) found `FlatProperPicardAlgebraicSpace.lean`, which supplies
  representability, the group structure, local finite presentation and immersion
  diagonal without the curve hypothesis. It does not assert smoothness or
  quasi-separatedness and is not an exact match for this node. Its already
  compiled universe-compatible group-functor pattern is reused.

No statement dispute or source correction. The example CompactObject module
requested by the brief is withdrawn in the current checkout; it contains no
remaining declarations. The current module follows the mandated module/public
import/exposed-section conventions directly.

Validation: scompile.py compiled both the sandbox and named library versions
successfully (3.3 s and 3.4 s); no diagnostics. All variables and the single
universe are explicitly bound; autoImplicit is disabled. Maximum line width 89.

## Second reading by NJ

This is the dispatcher's single-worker assignment, with other agents expressly
forbidden. I reread the completed file against the node and the four source
statements; the maintainer's independent review remains the independent reading.

The rereading checked the explicit proper/flat/fp binders, the residue-field
fibre bound, the universal canonical unit rather than a chosen arbitrary map,
and the exact Picard identification through the existing group-valued functor.
The small G and standard lifted natural isomorphism supply both the sheaf
identification and tensor-product law. The all-chart smoothness AND local-fp
clause includes both requested properties. The diagonal clause includes BOTH
quasi-compactness and immersion on scheme-valued representing tests; omitting
quasi-compactness, as in the earlier general flat-proper Picard theorem, would
have lost the quasi-separatedness assertion here. All four conclusions are
therefore present. No hypotheses, definitions, node statement, dependency list
or proof route needed correction after this rereading.
