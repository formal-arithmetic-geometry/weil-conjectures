## Worker report

The module `Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence` states
`AlgebraicGeometry.characterPicard_isogeny_sequence`, with its proof `sorry`.
It gives the entire character--Picard sequence, with the actual restriction and
pullback maps and the character descent characterization of its connecting map.
The five helper declarations in lean.declarations belong to the canonical arrows
of this node, as allowed by the human's missing-helper instruction. They introduce
no independently chosen data. No dependency, statement, proof, or accepted stage-1
split is changed. The inherited BLOCKED ending was a stage-1 resplitting refusal;
the stage-2 handoff rule in brief-stage2 §0 expressly permits this work.

Clause-by-clause correspondence:

* Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
  The algebraic-closure dependency explicitly includes algebraic closedness; an
  algebraic extension or a choice of an algebraic closure is not required here.
* F-group schemes: `G₁ G₀ : Over (Spec (.of F))`, with `[GrpObj G₁] [GrpObj G₀]`.
  The group structures are the dependency's existing Mathlib group objects.
* Affineness: `[IsAffine G₁.left] [IsAffine G₀.left]`.
* Finite type: `[LocallyOfFiniteType Gᵢ.hom] [QuasiCompact Gᵢ.hom]`, precisely
  the recorded dependency's conjunction, for i = 0,1.
* Smoothness: `[Smooth G₁.hom] [Smooth G₀.hom]`.
* Connectedness, including nonemptiness: `[ConnectedSpace G₁.left]` and
  `[ConnectedSpace G₀.left]`.
* Homomorphism: `(f : G₁ ⟶ G₀) [IsMonHom f]`, including unit and multiplication
  compatibility. Mathlib then supplies compatibility with inversion.
* Faithful flatness of coordinate rings: `f.left.appTop.hom.FaithfullyFlat`.
  Mathlib RingHom.FaithfullyFlat is Module.FaithfullyFlat for this scalar extension;
  flatness gives exactness and faithfulness detects zero modules.
* N is the scheme-theoretic kernel: `GrpObj.ker f`, with inclusion `GrpObj.kerι f`.
  Its existing construction is the pullback against the identity section.
* Finiteness: `IsFinite (GrpObj.ker f).hom`, equivalently finite-dimensional
  coordinate algebra over F by the group-scheme dependency's finite convention.
* Diagonalizability: `hdiag` gives a finite commutative group M and an isomorphism
  in `Grp (Over (Spec F))` from N to `Spec (MonoidAlgebra F M)` over F.
  Multiplicative notation for the abstract abelian group M identifies e^(m+n)
  with e^(mn). Mathlib's canonical group-algebra Hopf structure has exactly the
  displayed comultiplication, counit and antipode, and its canonical Spec group
  structure is used. This imposes no reducedness or prime-to-characteristic condition.
* X*(J): the literal existing Hom type
  `Additive (Grp.mk J ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`.
  There is no replacement character-group definition. The multiplicative group
  is the dependency's Laurent Hopf group. Mathlib's Hom.commGroup supplies
  pointwise multiplication; Additive writes it as addition. The exposed
  characterPicard_multiplicativeComm instance just routes the existing canonical
  Mathlib commutativity instance through the recorded multiplicative definition.
* Pic(J): `Additive J.left.Pic`, using the existing skeleton of invertible module
  sheaves and its tensor-product group law. Zero is the existing unit class of O_J.
* Character pullback and restriction: `characterPicard_precomp f` and
  `characterPicard_precomp (GrpObj.kerι f)`. Their data are the existing group-valued
  Yoneda map, hence precomposition with exactly these morphisms.
* Picard pullback: `(Scheme.Pic.mapHom f.left).toAdditive`, the existing pullback
  on invertible module classes.
* Connecting map: the existential `δ` is an additive homomorphism and
  `∀ χ, IsCharacterPicardDescentClass f χ (δ χ)` pins each value to character
  descent. This is not an unconstrained connecting map. The predicate uses an
  isomorphism f*L ≅ O_G₁ for the existing representative of the Picard class.
  Its inverse supplies the frame s. On EVERY test F-scheme T, every g:T→G₁ and
  every n:T→N, it requires s(gn) = χ(n)s(g). The regular scalar χ(n) is obtained
  by pulling back the Laurent coordinate t via the actual character morphism.
  Both sections are in (g f)*L, using pullbackComp and pullbackCongr. The binder
  h only supplies the equality transport; its equality follows for every g,n
  from IsMonHom f and GrpObj.kerι_comp. It is not an additional hypothesis on f.
  This is precisely the convention (g,z)n=(gn,χ(n)⁻¹z), because [gn,1]=χ(n)[g,1].
  All test schemes are allowed, so this specifies the full scheme-theoretic descent
  datum, including nilpotents. Evaluating at T=G₁×N and its projections recovers
  the whole action, rather than only its geometric points. A frame isomorphism
  identifies the entire trivial line, so equality on its generator is sufficient.
* The initial zero: `Function.Injective (characterPicard_precomp f)`.
* Exactness at X*(G₁): the first Function.Exact conjunct.
* Exactness at X*(N): the second Function.Exact conjunct, ending in δ.
* Exactness at Pic(G₀): `Function.Exact δ (Scheme.Pic.mapHom f.left).toAdditive`.
* The terminal zero: surjectivity of Picard pullback, the last conjunct.
  There are no extra normalization or uniqueness assertions beyond the specified
  maps, their character descent meaning and the exact sequence.

Dependencies inspected and used:

* Mathlib.Algebra.Field.Defs: Field, read with its full inherited ring/field structure.
* Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed, the algebraically-closed clause
  of def-weil-algebraic-closure (whose AlgebraicClosure construction is also recorded).
* Mathlib.CategoryTheory.Monoidal.Grp / .Cartesian.Grp: GrpObj, Grp, Grp.ofHom,
  GrpObj.ker, GrpObj.kerι, Hom.commGroup, yonedaGrpObj. Group-scheme conventions
  also read in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
* Mathlib.CategoryTheory.Monoidal.Mon: IsMonHom, unit/multiplication compatibility.
* Mathlib.AlgebraicGeometry.Morphisms.FiniteType / .QuasiCompact:
  LocallyOfFiniteType and QuasiCompact.
* Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth.
* Mathlib.Topology.Connected.Basic: ConnectedSpace.
* Sheaf.AlgebraicGeometry.StandardGroupSchemes: multiplicative, multiplicativeGroup;
  the full recorded construction and its source/docstring were read.
* Mathlib.AlgebraicGeometry.Scheme / .AffineScheme: Scheme, IsAffine, ΓSpecIso.
* WeilConjectures.AlgebraicGeometry.PicardFunctor / .Picard.Group: Scheme.Pic,
  Scheme.Pic.instCommGroup, Scheme.Pic.mapHom, with their full signatures and docs.
* Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra / .AlgebraicGeometry.Group.Affine:
  the real group algebra and its canonical Hopf/Spec group structures.
* Mathlib.RingTheory.RingHom.FaithfullyFlat: RingHom.FaithfullyFlat.
* WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit: pullbackΓ;
  Mathlib.AlgebraicGeometry.Modules.Sheaf: pullbackComp and pullbackCongr.
* Proof-only import WeilConjectures.AlgebraicGeometry.Descent supplies
  bijective_toDescentData_map, exists_isQuasicoherent_toDescentData_iso and
  isInvertible_of_toDescentData_iso from lem-pc-fpqc-descent.
  The two Borel proof dependencies have no Lean records yet; their proof plan is
  included in the docstring, and their imports must be added when they are stated.

Edge cases checked before and after writing:

* Identity isogeny: N is trivial, δ is zero, character and Picard pullbacks are
  identities. The frame condition has trivial action; no case is excluded.
* Trivial connected group Spec F is included; the group M may be the trivial group.
* [n]:G_m→G_m includes n divisible by the characteristic, with nonreduced μ_n.
  All test schemes in the frame condition are essential in this case. No smoothness
  is imposed on N, no nontriviality is imposed on χ, and no invertibility of n occurs.
* SL_p→PGL_p in characteristic p has the same permitted nonreduced μ_p kernel.
* Positive characteristic, characteristic zero and the zero character all remain.
  The zero character has the trivial descended class with invariant frame.
* Empty schemes are excluded exactly by the node's connectedness convention;
  they remain allowed as test schemes, where the equation holds on zero sections.
* All schemes and the field have universe u; modules/Picard classes live in u+1,
  as in the existing Picard interface. Quantifying over T in the same scheme
  universe includes G₁×N, enough to specify the full scheme-theoretic action.
  Finite groups have a model in Type u, so hdiag excludes no finite group.

Searches for existing declarations (all run for this item):

* msearch.py leanfinder: "Exact character Picard sequence for a faithfully flat
  isogeny of smooth connected affine algebraic groups with finite diagonalizable
  kernel". Eight results: cotangent Jacobi--Zariski sequences, ring-Picard units
  sequences and SnakeLemma.exact_δ'_left; no matching group-scheme theorem.
* msearch.py loogle: "GrpObj, Pic, character, isogeny". Zero hits, unknown identifier
  GrpObj on the remote service. Direct source inspection was used instead.
* msearch.py grep: "character|[Ii]sogeny|[Dd]iagonalizable" in AlgebraicGeometry.
  Thirteen unrelated characterization/characteristic hits; no matching theorem.
* msearch.py leansearch: "character groups Picard groups exact sequence algebraic
  group isogeny". Eight hits on ring Picard groups and ring-Picard exactness, not
  this statement or its character descent map.
* rg on lean/WeilConjectures and lean/Sheaf for MultiplicativeIsogeny,
  multiplicativeIsogeny, CharacterGroup, characterGroup, IsDiagonalizable,
  diagonalizable: no matches. A second search for characterPicard,
  IsCharacterPicardDescentClass and character.*[Pp]icard found only unrelated text.
* grep -rn of this item id in lean/WeilConjectures: no match.
* rg in dag/nodes for the character/isogeny notions found the Borel comparison,
  multiplicative-character-antiduality and other supporting theorem nodes, none
  with a usable Lean declaration of this exact statement. Existing Picard and group
  scheme definitions are used directly, with no new definition node required.

Source checked directly with pdftotext: Milne, printed pp.390--392, especially
Proposition 18.18 (129), its diagram and the preceding character sign convention.
The source agrees with the reviewed node. No STATEMENT-DISPUTED fault or statement
correction is needed.

Validation: scompile.py compiled the delivered file in sandbox and library-module
modes with no errors or non-sorry warnings. All auto-bound implicits are disabled.
Every proof is sorry; the definitions and instance contain real data only.

## Second reading by Q91

A separate rereading pass in this worker session (the dispatcher expressly forbids
starting another agent) compared the final Lean, node and Milne source. Each
hypothesis and each of the five exactness conditions is matched above. The added
frame predicate was checked separately: it uses the representative of δχ itself,
its actual pullback, all scheme-valued n, and the χ(n) scalar rather than its inverse,
consistent with [gn,1]=χ(n)[g,1]. The h equality is always available from the kernel
and homomorphism equations. Thus the connecting map is tied to the specified
line bundle and does not replace it by arbitrary additive data. Character maps
are literally Yoneda precomposition; Picard pullback is the pre-existing mapHom.
The kernel model uses the group-algebra Hopf structure, not just an isomorphism
of underlying schemes. The initial and final zero clauses, nonreduced kernels,
trivial character, identity map, and small-universe test family were checked.

The initial elaboration probe exposed two namespace issues (pullbackΓ belongs
to AlgebraicGeometry) and the need to expose the existing Laurent Hopf group's
commutativity through the dependency abbreviation. Both are resolved in the final
source; no mathematical hypothesis was added to address them. No remaining
hypothesis or conclusion mismatch was found. The two unstated Borel proof nodes
were not duplicated. The accepted stage-1 split is preserved verbatim.
