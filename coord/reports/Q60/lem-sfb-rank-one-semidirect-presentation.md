## Worker report

The delivery states `AlgebraicGeometry.RankOnePresentation.rank_one_semidirect_presentation`
in `Sheaf.AlgebraicGeometry.GroupScheme.RankOneSemidirectPresentation` with one `sorry`.
The two real helper definitions `matrix` and `conjugatedMatrix` only spell out the
matrix coordinates and the conjugation already specified in this node. Neither selects
unspecified data. No new definition node, dependency repair or statement correction is needed.

Source read: Milne, Algebraic Groups (2017), Proposition 20.32 and Theorem 20.33 with
Corollary 20.34, printed pp.418--419; paragraphs 21.19 and 21.23--21.24, printed
pp.431--432. The node is the explicit semidirect presentation built from the maps of
21.24, rather than the erroneous unrestricted wording in the first line of 20.33.
The node's seven accepted proof steps are reproduced in the theorem docstring,
including the two principal charts and the arbitrary-algebra kernel calculation.

Hypotheses, matched individually:

- `F : Type u`, `[Field F]`, `[IsAlgClosed F]` give the algebraically closed field.
- `H T : Grp (Over (Spec (.of F))))` are actual group schemes over F.
  `hH : ReductiveTorusCentralizer.IsReductive H` includes smoothness,
  geometric connectedness, affineness and finite type, and trivial unipotent radical.
- The group-scheme homomorphism `i : T ⟶ H` and `hT : IsMaximalTorus i`
  give the specified maximal torus subgroup. `hsplit` states its isomorphism to
  `MultiplicativeType.splitTorus F r` for some unrestricted natural number r.
- `aH` is its action on H and `haH` identifies this action with conjugation by i.
  Thus all weights below are actual torus character weights.
- The character `α` is the node's γ. `δ` and `hδ` specify the inverse character,
  i.e. -γ in additive character notation. `hroots` states that the full root set
  `RankOneRoots.roots T H aH` consists exactly of those two characters.
  In particular α is nontrivial; no separate or stronger root condition is imposed.
- `uPlus` and `uMinus` are the parametrized root subgroup inclusions Ga → H.
  `hPlus`/`hMinus` require closed subgroup embeddings, stability under T, and
  differential range exactly the α/δ weight space. The recorded root-subgroup
  theorem uniquely identifies these with Uγ and U-γ. Since the domains are Ga,
  these embeddings are precisely parametrizations by isomorphisms onto those subgroups.
- `ν : RankOneRoots.Cocharacter T` is the given coroot, and
  `v : Grp.mk (LinearGroupSchemes.specialLinear F 2) ⟶ H` is the specified
  group-scheme homomorphism. `hvPlus`/`hvMinus` identify its restrictions on
  matrices `!![1,z;0,1]` and `!![1,0;z,1]` with `uPlus`/`uMinus`.
  `hvDiag` is exactly v(diag(s,s^-1)) = ν(s) in H. These conditions identify the
  cocharacter with the coroot of this rank-one map, as in Milne 21.24; no arbitrary
  cocharacter satisfying only a numerical pairing is substituted.
- Each restriction formula quantifies over every `A : CommAlgCat.{u} F`, so
  these are scheme-theoretic identities, including on nonreduced algebras.
  The common universe is the existing affine-scheme coefficient convention;
  every affine coordinate algebra of the schemes concerned has this size.

Conclusions, matched individually:

- `C : T.X ⊗ specialLinear F 2 ⟶ specialLinear F 2` is a genuine scheme
  morphism. The first point formula pins all four entries to `conjugatedMatrix α`.
  Its entries are a, α(t)b, α(t)^-1 c, e, exactly conjugation by diag(α(t),1).
  Inverse units are evaluated as Laurent coordinates of the inverse Gm point.
- The existential bundled group scheme `E` has an underlying-scheme isomorphism
  `eE : specialLinear F 2 ⊗ T.X ≅ E.X`. This identifies E with the precise
  product scheme in the node; it introduces no arbitrary replacement space.
  The multiplication formula transports E's multiplication back along eE and
  states `(M,t)(N,z) = (M C(t)(N), tz)` for every algebra. A group object's
  multiplication determines its identity and inverse, so this pins the full law.
- `IsAffine E.X.left`, `LocallyOfFiniteType E.X.hom`, and `QuasiCompact E.X.hom`
  assert affine finite type, without a chosen dimension or characteristic.
- `π : E ⟶ H` is a homomorphism in the bundled category of group schemes.
  `eE.hom ≫ π.hom.hom = (fst ≫ v.hom.hom) * (snd ≫ i.hom.hom)`
  specifies exactly the morphism `(M,t) ↦ v(M)t`, as a morphism equality.
- `Module.FaithfullyFlat` uses exactly `π.hom.hom.left.appTop.hom.toAlgebra.toModule`.
  Thus it is faithful flatness of Γ(E) over Γ(H) through the coordinate map π*,
  rather than only flatness or surjectivity on rational points. Mathlib's predicate
  is the standard exact, zero-detecting extension of scalars.
- `e : Grp.mk Gm ≅ Grp.mk (GrpObj.ker π.hom.hom)` is an actual group-scheme
  isomorphism to the categorical kernel (the fibre product with the unit).
  Its composite with the kernel inclusion and `eE.inv` has first-coordinate matrix
  diag(s,s^-1) and second coordinate `(s ≫ ν.hom.hom)^-1` on every algebra.
  These two formulas determine exactly kγ, not just an unspecified kernel isomorphism.
- The final identity is `v(C(t)(M)) = i(t) v(M) i(t)^-1` on every algebra.
  All participating maps are scheme morphisms; affine Yoneda identifies this
  natural point equality with the scheme-morphism equality in the node.

Dependency declarations read and used:

- Mathlib `Field`, `Algebra/Field/Defs.lean:180`, and `IsAlgClosed`,
  `FieldTheory/IsAlgClosed/Basic.lean:62`; the latter matches the algebraic-closure
  node's explicitly recorded algebraically closed predicate.
- `CategoryTheory.GrpObj`, `Grp`, `IsMonHom` and their group-valued Hom functors,
  recorded on def-sc-group-scheme. The actual `GrpObj.ker` and `kerι` are the
  existing pullback construction in
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure`,
  `AlgebraicGeometry.reductive_borel_pair_structure`: split maximal tori and the
  actual character root datum. Its public terminology supplies
  `ReductiveTorusCentralizer.IsReductive` and `IsMaximalTorus`; their definitions
  were read, including the geometric connectedness convention.
- `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRootSubgroupParametrizations`,
  `TorusCharacterTangent.reductive_root_subgroup_parametrizations`,
  `additiveParameterPoint`, `weightSpace` and `IsStable`: the unique normalized
  Ga subgroup with the prescribed tangent image and its coordinate parametrization.
- Added the already landed `def-sfb-rank-one-root-interfaces` to stmt_deps:
  `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces` supplies
  `RankOneRoots.Character`, `Cocharacter`, `roots`, `adjointMap` and
  `multiplicativeValue`. This reuses exactly the dependency's character-weight
  and Laurent-coordinate conventions, including in positive characteristic.
- Added the already landed `def-sc-general-linear-group` to stmt_deps:
  `Sheaf.AlgebraicGeometry.LinearGroupSchemes` supplies `specialLinear`,
  `specialPoints` and its naturality. The definition is the actual polynomial
  quotient by determinant minus one. Its index is `ULift (Fin 2)`; the helper
  `matrix` just reads the four entries using lifted Fin indices. It is not a second
  special linear group or a new point-equivalence choice.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`, `Module.FaithfullyFlat`, is the
  faithful-flat module predicate also used by the recorded affine-image theorem.
- Proof-only imports include `BorelRootProductCoordinates`, `BruhatLongestCellCharts`,
  `AffineHomomorphismFlatImage` and `ReductiveRankOneReflections`, with their recorded
  declarations. The regular-cocharacter Borel description and smooth-subgroup
  tangent-generation nodes have no Lean records in the read snapshot; they are
  proof-only prerequisites, so no missing notion is required for this statement.
  Their modules are not invented or imported.

Edge cases checked before writing:

- H=SL2, T its diagonal torus: α(s)=s², ν(s)=diag(s,s^-1), v=id.
  The kernel is the graph of ν^-1, even though α is not a primitive character.
- H=PGL2 in characteristic 2: ν can have infinitesimal kernel μ2. The graph map
  into SL2×T is nevertheless a Gm embedding because of its first component;
  the actual categorical kernel and all-algebra formulas retain μ2 information.
  No separability or characteristic-zero assumption appears.
- H=GL2 and products with an arbitrary split central torus: root-set rank one
  does not force dim(T)=1. `hsplit` leaves r arbitrary, and the multiplication
  and kernel formulas retain all central factors.
- The trivial torus/empty root set cannot satisfy `hroots` (α would have to be
  a nontrivial weight); their exclusion is already the node's two-root hypothesis.
- A=0 and nonreduced test algebras are allowed by CommAlgCat. The formulas are
  polynomial/Laurent identities, not field divisions or assertions only on F-points.
- The SL2 coordinate charts cover because ae-bc=1, but there is no false assumption
  that elementary matrices generate SL2(A) globally. That argument is confined to
  the proof docstring's principal-open calculation.

Searches performed (all no exact match):

- msearch leanfinder: "A split rank one reductive group scheme is a faithfully flat
  semidirect quotient of SL2 times its maximal torus". Eight results: abstract
  SpecialLinearGroup center results and SemidirectProduct.inr_splitting; none gives
  this affine scheme presentation, coordinate faithful flatness or coroot kernel.
- msearch loogle: "SpecialLinearGroup, SemidirectProduct". Zero hits.
- msearch grep, Mathlib/AlgebraicGeometry: "semidirect|specialLinear|SL2". Zero hits.
- msearch leansearch: "A rank one reductive group scheme is a faithfully flat
  quotient of SL2 semidirect its maximal torus with kernel the coroot multiplicative
  group". Eight results on abstract SL groups, Lie coroots and root pairings;
  none matches this theorem.
- rg on project Sheaf and upstream WeilConjectures AlgebraicGeometry:
  "semidirect|Semidirect|specialLinear|SL2|rank.one.semidirect". Found and reused
  LinearGroupSchemes and RankOneRootInterfaces. The existing cocharacter-limit
  semidirect formula concerns different subgroups, not the SL2 presentation.
  Upstream LinearAlgebraicGroup/RankOne concerns monodromy split cyclic extensions.
- Exact node-id search in upstream WeilConjectures found no declaration.
- Full-name/helper-name search in Mathlib, Sheaf, WeilConjectures and
  dag/lean_names_upstream.json for RankOnePresentation,
  rank_one_semidirect_presentation and conjugatedMatrix found no collisions.

No STATEMENT-DISPUTED flag and no node fault. The only node changes are its `lean`
record and the addition of the two already landed notion nodes to `stmt_deps`.

Validation: scompile.py compiled both the sandbox and actual library module names
cleanly under the required per-file time limit. The initial source-level elaboration
issues were repaired before delivery. No theorem is proved; both helper definitions
contain real coordinate expressions. Every variable/universe is explicit and
`autoImplicit` is disabled.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
