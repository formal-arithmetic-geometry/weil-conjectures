## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport` states
`AlgebraicGeometry.Scheme.Modules.exists_finitePresentation_closedImmersion_fiber_support`.
Its only theorem proof is `sorry`. The node changes only in `lean`; there are no new
nodes, dependency repairs, statement corrections, or disputed assertions.

Source read: `literature/stacks-project/flat.tex`, lemma-sheaf-lives-on-subscheme,
Tag 057Q, lines 445–491, including the full proof. This item is a supporting lemma,
not the blueprint unit's own statement.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`; their affineness: `[IsAffine X] [IsAffine S]`.
- The morphism f: `(f : X ⟶ S)`; finite type:
  `[LocallyOfFiniteType f] [QuasiCompact f]`, as the recorded definition prescribes.
- The sheaf F: `(F : X.Modules)`; finite type: `[F.IsFiniteType]`;
  quasi-coherence: `[F.IsQuasicoherent]`. No coherence or Noetherian hypothesis is added.
- The chosen point: `(x : X)`. Every occurrence of s is the explicit expression `f x`;
  there is no independent point or condition that x belong to Supp(F).
- The residue-field scheme and its canonical map are `Spec (S.residueField (f x))`
  and `S.fromSpecResidueField (f x)`.
- The fibre X_s is `Limits.pullback f (S.fromSpecResidueField (f x))`.
  Its map to X is `pullback.fst f (S.fromSpecResidueField (f x))`.
- F_s is the image of F under `tensorPullback` of that projection, exactly the
  dependency's tensor-formula pullback, rather than Mathlib's different `Modules.pullback`.
- Existence of Z and j is `∃ (Z : Scheme.{u}) (j : Z ⟶ X)`.
  The closed immersion condition is `IsClosedImmersion j`.
- Finite presentation of j is the conjunction `LocallyOfFinitePresentation j ∧
  QuasiCompact j ∧ QuasiSeparated j`, including both global finiteness conditions.
- The sheaf H is `∃ H : Z.Modules`; the next two conjuncts are `H.IsFiniteType`
  and `H.IsQuasicoherent`.
- The required pushforward isomorphism is `Nonempty ((pushforward j).obj H ≅ F)`.
  `Scheme.Modules.pushforward` is the existing sectionwise pushforward;
  `pushforward_obj_obj` identifies its sections on V with H(j⁻¹V), exactly the
  node's explanatory last sentence, so no extra tautological conclusion is appended.
- Z_s is the source of the displayed `pullback.map`: the pullback of `j ≫ f` and
  the same canonical residue-field map. Its target is X_s, and its components
  are j and the identity on Spec κ(s), over the identity on S. The two `by simp`
  arguments supply the commuting identity squares only.
- Its underlying subset of X_s is `Set.range (...).base`. Since j is a closed
  immersion, its base change is a closed immersion, so this is exactly the
  underlying closed subset in the node, without selecting an arbitrary embedding.
- The right side of the equality is the set of z with
  `¬ Subsingleton (((tensorPullback ...).obj F).presheaf.stalk z)`.
  Non-subsingleton of an additive-group stalk means it is not the zero module.
  This states equality of underlying subsets, not an unwarranted equality of
  schemes or an equality involving a chosen scheme structure on the support.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact` as specified by def-weil-finite-type-morphism.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  the recorded definition also requires `QuasiCompact` and `QuasiSeparated` for
  finite presentation.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`, `pullback.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, and the canonical `Scheme.fromSpecResidueField`.
- `WeilConjectures.AlgebraicGeometry.Coherent`: its pqf-def-coherent interface
  explicitly identifies quasi-coherence and finite type with Mathlib's
  `SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`, used here.
  The dependency's coherent predicate itself is not an assumption of this lemma.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `Scheme.Modules.tensorPullback`, with its actual tensor-formula object construction.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj` use Mathlib's additive stalk
  carriers. The inline `.presheaf.stalk` here is that very carrier, following the
  project's support convention, with no duplicate stalk construction.

The published versions of the three upstream dependency modules absent from the
local source checkout were read using `scompile.py --source`. The same command
read all four upstream proof-only modules imported here. All recorded statement
modules are public imports. Proof-only imports give the affine tilde/global-sections
adjunction and pushforward formula (`Mathlib.AlgebraicGeometry.Modules.Tilde`),
affine fibre products (`Mathlib.AlgebraicGeometry.Pullbacks`), the finite-type-over-
a-field Noetherian facts (`Mathlib.RingTheory.FiniteType` and
`Mathlib.RingTheory.Spectrum.Prime.Noetherian`), and the recorded upstream modules
`FiniteTypeModuleSupportClosed`, `QuasicoherentFiniteTypeAffine`,
`FiniteTypeModuleSupportPullback`, and `TensorPullbackTilde`. The docstring carries
all five steps of the node's proof and names every proof dependency.

Edge cases checked against the affine proof:

- F = 0: choose J = (1), Z empty and H = 0; both fibre subsets are empty.
- F = O_X: J = 0 and Z = X work; both fibre subsets are the whole fibre.
- x need not be in the support. No nonzero-stalk assumption on x appears.
- Empty X: the assertion quantified over x is vacuous, exactly as in the source;
  empty Z remains allowed even when X has a point.
- Non-Noetherian A or B and infinitely generated Ann(M) are allowed. Only its
  extension to the finite-type algebra over κ(s) needs finite generation; the
  construction chooses a finite subideal J, not Ann(M) itself.
- Nilpotent structure on Z_s is unrestricted: the conclusion is set-theoretic.
- The zero-dimensional/empty finite generator list is allowed. There are no
  assumptions on characteristic, reducedness, algebraic closure, or dimension.
- `universe u` is explicit, as are all binders. No test-object quantification or
  artificial independent smaller universe is introduced.

Searches for an existing statement:

- `msearch.py leanfinder`, query “A finite type quasi coherent sheaf on an affine
  finite type scheme is the pushforward of a finite type sheaf on a finitely
  presented closed subscheme whose fibre is its support”: eight hits on
  quasicoherent finite presentations and finite morphisms; none states Tag 057Q.
- `msearch.py loogle`, query
  `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation`:
  zero hits.
- `msearch.py grep`, query
  `support.*(finite[Pp]resentation|[Cc]losed)|exists.*[Cc]losed.*[Ss]ubscheme`,
  directory `AlgebraicGeometry`: eleven hits concerning ideal-sheaf support,
  normalization, and closed immersions; no matching theorem.
- `msearch.py leansearch`, query “finite type quasi coherent sheaf pushforward
  finite presentation closed immersion fibre support”: eight hits about
  quasi-coherent finite presentations, no supporting closed subscheme theorem.
- `rg` in the upstream `WeilConjectures` tree and side `lean/Sheaf`, for the
  blueprint id, `sheaf.lives.on.subscheme`, `finite_type_sheaf_fp_support`, and
  support/finite-presentation combinations: only the unrelated support-reduction
  filtration theorem appeared. Broader upstream support-existence matches concern
  divisors, dense points, and ample sheaves, rather than this assertion.
- The chosen declaration name was searched in `dag/lean_names_upstream.json`,
  Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf`: no collision.

Validation: the prescribed `scompile.py` single-file compilation was used. The initial
attempts found a namespace collision (`Modules.pullback` versus `Limits.pullback`),
a line-break parsing error at a projection, and category inference of the fibre
carrier as a type-category pullback. Explicit `(C := Scheme.{u})` repairs the last
ambiguity. These were corrected without
changing the mathematical statement. Final compilation and delivery preflight
are recorded by the delivery wrapper.

## Second reading by NW

Author self-check under the dispatcher's direct-delivery instructions; this is
not an independent agent review. The maintainer performs the independent review.
I reread the node, Stacks 057Q, and the complete module. The binders retain both
affine schemes, finite type of f, finite type and quasi-coherence of F, and the
arbitrary point x. The witnesses retain Z, its closed immersion of finite
presentation, and H with both finiteness properties and the pushforward
isomorphism. The last equality compares the canonical base-change image with
the actual tensor-pullback stalk support on X_s. The node's section formula is
already the definition of the imported pushforward. No hypothesis or clause was
lost, and no source-based node correction was necessary. The self-check found
and repaired only the elaboration issues recorded above; no new definitions or
postponed helper theorems were introduced.
