## Worker report

The module `Sheaf.AlgebraicGeometry.CentralInfinitesimalTorusExtension` states
`AlgebraicGeometry.MultiplicativeType.central_infinitesimal_torus_extension` with
one `sorry`, and introduces no definitions. The node's statement is unchanged.
Source read: Milne, Algebraic Groups (2017), printed pp.238--240, especially
Corollary 12.22 and Theorem 12.23 (PDF pp.250--252). The central commutator descent
is the explicit supporting argument in the node, not a claim that Milne separately
states this supporting lemma. The current blueprint root was checked at
`literature/blueprint/latest`; this supporting synthesis has no own blueprint unit.
The prescribed CompactObject example is now withdrawn and contains no declarations;
its node's current record is the existing upstream declaration
`CategoryTheory.IsCompactObject` in `WeilConjectures.CategoryTheory.CompactObject`. The delivered header follows the
current module-mode requirements and the neighboring character-antiduality module.

Hypotheses, clause by clause:

- The field is `{k : Type u} [Field k]`. The fixed algebraic closure is the recorded
  `AlgebraicClosure k`, used inside `IsTorus` and `IsMultiplicativeType`.
- `E T : Grp (Over (Spec (.of k)))` are actual group schemes. Their homomorphism
  is `q : E ⟶ T`, whose underlying Over morphism is `q.hom.hom`.
- `[IsAffine E.X.left]` and `[IsAffine T.X.left]` state affineness. Each pair
  `[LocallyOfFiniteType _.X.hom] [QuasiCompact _.X.hom]` states finite type.
- `hT : IsTorus T` is exactly the recorded geometric split-torus definition.
- `hqfinite : q.hom.hom.left.appTop.hom.Finite` states module finiteness of the
  coordinate map k[T] to k[E]; `hqflat : ...FaithfullyFlat` states faithful flatness
  for precisely this ring map, not an unrelated algebra structure.
- N is always the actual scheme-theoretic `GrpObj.ker q.hom.hom`. It is not an
  arbitrary subgroup, a kernel on rational points, or an assumed presentation.
- `hlocal : IsLocalRing Γ((GrpObj.ker q.hom.hom).left, ⊤)` states locality of k[N].
- In `hnil`, the identity section `MonObj.one (X := GrpObj.ker q.hom.hom)` pulls
  global sections back to Γ(Spec k); `Scheme.ΓSpecIso` then identifies these with k.
  `RingHom.ker` of this composite is exactly the augmentation ideal, and
  `IsNilpotent` means some power of this ideal is zero. The terminal Over object
  has underlying scheme Spec k; this expression elaborates without any cast.
- `hcentral` quantifies over every commutative k-algebra A in the field/scheme
  universe, and every A-valued n in N and e in E, and says
  `Commute (n ≫ GrpObj.kerι q.hom.hom) e`. This retains nonreduced test algebras.
  There is no smaller independent test universe. This is the standard size
  convention of the recorded group-scheme functor of points; larger tests are
  detected by the affine coordinate/universal-point condition in this universe.
- `hN : IsMultiplicativeType (Grp.mk (GrpObj.ker q.hom.hom))` uses the same
  multiplicative-type definition as the statement dependency.

Conclusions, clause by clause:

- `IsCommMonObj E.X` says that E is commutative as a group scheme.
- `IsMultiplicativeType E` is the required geometric multiplicative-type property.
- For every `ks` with `[Field ks] [Algebra k ks] [IsSepClosure k ks]`, the three
  objects `MT ME MN : CharacterModules k ks` are finitely generated additive
  abelian groups with Galois actions having open stabilizers, hence continuous
  for the discrete topology. The three equivalences `eT eE eN` identify their
  elements bijectively with the exact `GeometricCharacters` of T, E, and N.
  The target in that recorded definition is the scalar extension of G_m,k,
  canonically G_m,ks; it includes all group-scheme homomorphisms.
- Each equivalence is explicitly required to send addition to pointwise
  multiplication of the underlying Over morphisms. Thus these are identifications
  of character groups, not merely equal-cardinality auxiliary groups.
- The three `IsConjugate` clauses identify the actions with the recorded canonical
  coefficient-conjugation action, rather than allowing arbitrary Galois actions.
- `p : MT.obj.V →+ ME.obj.V` and `r : ME.obj.V →+ MN.obj.V` are specified by the
  equalities `eE (p x) = baseChange.map q ≫ eT x` and
  `eN (r x) = baseChange.map (Grp.ofHom (GrpObj.kerι ...)) ≫ eE x`.
  These determine exactly pullback and restriction. They are not arbitrary maps
  selected only to make an exact sequence exist. Both explicit equivariance
  clauses make these homomorphisms maps of Galois modules.
- `Function.Injective p ∧ Function.Exact p r ∧ Function.Surjective r` renders
  the entire sequence 0 → X*(T) → X*(E) → X*(N) → 0. `Function.Exact` identifies
  the kernel of r with the image of p, with zero in the additive target.
- `Module.Free ℤ MT.obj.V ∧ Module.Finite ℤ MT.obj.V` renders free of finite rank;
  `Finite MN.obj.V` renders finite X*(N). All three groups are finitely generated
  already by membership in `CharacterModules`.
- There is no smoothness, reducedness, perfection, characteristic, connectedness,
  or algebraic-closedness hypothesis on k, E or N.

Dependency declarations read and used:

- Mathlib `Field`, `AlgebraicClosure` (with its field and algebraic-closure
  structures), `LocallyOfFiniteType`, and `QuasiCompact`, from their recorded files.
- `CategoryTheory.GrpObj`, `Grp`, `IsCommMonObj`, `Grp.ofHom`; the group's Over
  encoding, `GrpObj.ker`, `GrpObj.kerι` and the identity section are documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and the imported upstream
  `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `IsTorus`,
  `IsMultiplicativeType`, `baseChange`, with their actual full signatures read.
- `WeilConjectures.Mathlib.FieldTheory.IsSepClosed`:
  `IsSepClosure.exists_intermediateField_mem`, including its docstring identifying
  the notion with Mathlib's `IsSepClosure`; the theorem is not restated.
- `Sheaf.AlgebraicGeometry.MultiplicativeCharacterAntiduality`:
  `multiplicative_character_antiduality`, read in full. It publicly exposes the
  existing `MultiplicativeCharacterData` declarations `CharacterModules`,
  `GeometricCharacters`, `IsConjugate`. The already landed definition node
  `def-sfb-multiplicative-character-data` is added to stmt_deps for these notions.
  No dependency interface needs repair.
- Plain proof imports include the stated commutative-extension theorem, the
  upstream faithfully flat Amitsur exactness theorem, tensor product maps, faithful
  flat universal injectivity, the closed-immersion criterion, and the group-like
  basis theorem. Proof nodes not yet carrying Lean records are named in the
  proof docstring and are not invented or assumed as new hypotheses.

Edge cases checked mathematically before writing:

- Rank-zero torus: E = N is a finite infinitesimal multiplicative group; the first
  character group is zero and restriction is an isomorphism. No positive rank is
  imposed; `Module.Free` includes the zero module.
- Trivial kernel, including q = identity: restriction targets the zero character
  group and pullback is an isomorphism. Its augmentation ideal is zero, a
  nilpotent ideal, and k is local.
- Characteristic p: q : G_m → G_m, t ↦ t^p has kernel μ_p. Its coordinate ring is
  local with nilpotent augmentation ideal despite being nonreduced. The resulting
  sequence is 0 → Z → Z → Z/p → 0 with first map multiplication by p. Every
  hypothesis and conclusion here permits this example.
- In characteristic zero an infinitesimal multiplicative kernel is trivial; no
  characteristic assumption accidentally rules out this case.
- Nonperfect k and nonsplit tori are allowed. Characters are taken over a
  separable closure, not merely over k and not only on geometric rational points.
- The empty scheme cannot be a group scheme over a field because it would lack
  an identity section; it is not excluded by an added hypothesis.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: “A central extension of a torus by an
  infinitesimal group of multiplicative type is commutative and has a short exact
  character sequence”. Eight unrelated hits, chiefly LieAlgebra.Extension and
  LieAlgebra.ofProd; no matching group-scheme statement.
- `msearch.py ... loogle` query: `"IsCommMonObj", "Exact"`: zero hits.
- `msearch.py ... grep` query: `infinitesimal|multiplicative.type|torus`, subdirectory
  AlgebraicGeometry: two hits in FormallyUnramified, neither relevant.
- `msearch.py ... leansearch` query: “Central infinitesimal extensions of tori and
  exact character groups”. Eight hits about ring extensions, MulChar, and the
  unrelated additive CharacterModule; no match.
- `rg` of WeilConjectures and Sheaf for
  `central_infinitesimal|infinitesimal.*torus|torus.*infinitesimal`: no result;
  search for this exact blueprint id in WeilConjectures: no result.
- Targeted rg for centrality, augmentation, GeometricCharacters and IsConjugate
  found the existing character interface and centrality-on-algebras conventions
  used here, but no theorem proving the present statement.

The module compiled in both sandbox and library module modes through the prescribed
scompile.py, without errors or warnings. No source clone files were edited and no
Git commands or global builds were run directly. No STATEMENT-DISPUTED issue found.

## Second reading by Q118

A second self-reading matched the node and final signature clause by clause above.
The first compile exposed a pipeline-parenthesization error in the canonical
restriction expression; it was replaced by the direct equality of group-scheme
morphisms. Both canonical maps now use actual compositions after scalar extension.
The augmentation uses the identity section of the actual kernel and the canonical
ΓSpec identification; it is not an arbitrary residue map. The existential character
models are constrained by bijective character identifications, addition, conjugation,
and canonical-map equations, so the exactness conclusion concerns the specified
character sequence. Finite rank and finite kernel characters are both present.

The dispatcher explicitly forbids starting another agent. This is therefore a
self-review, not an independent worker review; the maintainer's independent review
is the separate review required by the dispatch brief. No independent reviewer is
claimed here. No new nodes or dependency modules, and no statement correction.

Validation: deliver2.py --no-push returned `OK (dry run)` at 383f3f1fd8e,
with preflight and both module-mode compiles passing.
