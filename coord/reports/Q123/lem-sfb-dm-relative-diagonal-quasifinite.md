## Worker report

The module `Sheaf.AlgebraicGeometry.DMRelativeDiagonalQuasiFinite` states
`CategoryTheory.dm_relativeDiagonal_locallyQuasiFinite`, with proof `sorry`.
It introduces no definitions and proves nothing. The natural-language node, its
source and its proof plan are unchanged. Its `stmt_deps` gains the already landed
`def-sfb-dm-stack-morphism-properties`, which owns the canonical relative diagonal
and the algebraic-space property test. No new node or dependency repair is needed.

Clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`.
- The two stacks over S are `F : BasedCategory.{v₁, w₁} (Over S)` and
  `G : BasedCategory.{v₂, w₂} (Over S)`. Their category and hom universes are
  independently quantified. `hF` and `hG` assert exactly
  `IsDeligneMumfordModuliStack F` and `IsDeligneMumfordModuliStack G`, including
  stack descent, algebraic-space diagonal and surjective etale scheme atlas.
- An arbitrary morphism over S is `f : BasedFunctor F G`. There are no
  local-finite-type, separatedness, representability, or atlas assumptions on f.
- The specified map to `F ×_G F` is the existing `moduliRelativeDiagonal f`.
  Its actual construction sends x to (x,x,id) and an arrow to its repeated pair.
  Its codomain is the existing `moduliTwoFiberProduct f f`, not a product over S.
- The conclusion is `ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite
  (moduliRelativeDiagonal f)`. Opening this definition, it quantifies over every
  `T : Over S` and `t : BasedFunctor (discreteModuli (yoneda.obj T))
  (moduliTwoFiberProduct f f)`. It produces an algebraic space Z, an actual
  projection `p : Z.obj.obj ⟶ yoneda.obj T`, and
  `HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p`. The latter is an
  equivalence with the actual 2-pullback and a 2-isomorphism identifying the
  specified projection. Thus representability is included in the conclusion;
  no representability is being assumed.
- For every `U : Over S` and `a : yoneda.obj U ⟶ Z.obj.obj`, it assumes only
  `AlgebraicSpace.IsEtale a` and concludes
  `Scheme.Hom.IsLocallyQuasiFinite (yoneda.preimage (a ≫ p)).left`.
  This is exactly every representable etale scheme chart and its composite to T.
  No surjectivity of a is required. The recorded scheme predicate means
  `∀ x, IsQuasiFiniteAtPoint ... x`; its affine-ring definition includes finite
  type and quasi-finiteness at the corresponding prime, exactly pqf-def-quasifinite.
  The representative is existential because the notion is defined up to an
  equivalence over T; all of its charts are tested. Changing representative
  transports the same condition over T, so this is the intrinsic assertion.
- Etale and smooth are contextual definitions in the node rather than additional
  hypotheses on f. The inherited DM/atlas predicates use the recorded scheme
  etaleness. There is no smoothness assumption or smoothness conclusion to add.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  the base and all test schemes are the recorded schemes.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsDeligneMumfordModuliStack`, `moduliTwoFiberProduct`,
  `HasSpaceBaseChange`, `discreteModuli`, `ModuliTwoIso`. Read their complete
  definitions: presentations retain equivalence and projection compatibility.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`
  and `AlgebraicSpace.IsEtale`; these are the recorded fppf sheaves with
  representable diagonal and etale atlas, and representable scheme-test etaleness.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  Read their affine-local signatures. Both come through the stack interfaces.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite` and
  `IsQuasiFiniteAtPoint`. This avoids Mathlib's weaker predicate omitting finite type.
- Added landed definition `def-sfb-dm-stack-morphism-properties`, module
  `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.moduliRelativeDiagonal` and `ModuliSpaceTest`. Read their
  signatures, data and docstrings. A traversal of both dependency edge kinds
  found no path from this added definition to the item (9768 nodes visited).

The four steps of the node's proof are included in the theorem docstring. Plain
proof imports are the recorded modules for `lem-sfb-dm-isom-space-unramified`
(`CategoryTheory.dm_isom_space_unramified`), `def-trf-scheme-algebraic-space`
(`AlgebraicSpace.schemeSpace` in `EnlargedEtaleRingedSite`),
`lem-trf-space-fibre-products-etale-covers`
(`AlgebraicSpace.fibreProduct_isAlgebraicSpace` in
`AlgebraicSpaceFibreProductsEtaleCovers`), and
`lem-weil-pbc-unramified-quasi-finite-at-points`
(`Scheme.Hom.isLocallyQuasiFinite_of_unramified` in
`WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite`). Their relevant
signatures and source docstrings were opened. The remaining proof-only node,
`lem-sfb-space-unramified-permanence`, has no lean or mathlib_match record in the
read clone, so has no recorded module to import. It is cited in the proof docstring;
no missing statement notion depends on it, and no duplicate theorem is introduced.

Source and edge checks: read stacks-morphisms.tex, Tag 050N,
`lemma-separated-implies-morphism-separated`, especially parts (2), (5), (6).
The source actually gives unramified relative diagonal in the DM case, so local
quasi-finiteness is the stated consequence. The item is an auxiliary node, not a
blueprint unit statement. The base and test schemes can be empty; every chart is
quantified even when empty or not surjective. For f the identity, the relative
diagonal is an equivalence and the tested projections are etale. For scheme
stacks the diagonal is locally an immersion at every source point, hence is
locally quasi-finite without f being locally of finite type. For a finite etale group G, BG -> S is a nonrepresentable
example whose diagonal tests are G-torsors; the theorem admits it. No
quasi-compactness or global finiteness is claimed. No characteristic is restricted,
and stack universes are independent of each other and of the scheme universe.
No statement fault or STATEMENT-DISPUTED flag was found.

Searches (using the prescribed msearch wrapper unless
explicitly marked rg):

- leanfinder: `The relative diagonal of a morphism of Deligne Mumford stacks is
  locally quasi finite`: eight hits, including scheme LocallyQuasiFinite
  composition, quasi-separated diagonals, pullback projections and formally
  unramified scheme diagonals; no stack theorem.
- loogle: `"LocallyQuasiFinite"`: twelve scheme hits, including
  `AlgebraicGeometry.LocallyQuasiFinite` and its permanence instances; no stack
  relative-diagonal theorem and the scheme predicate is weaker than Stacks 01TD.
- grep (Mathlib/AlgebraicGeometry):
  `DeligneMumford|moduliRelativeDiagonal|relative.*diagonal`: zero hits.
- leansearch: `The relative diagonal of any morphism between Deligne Mumford
  stacks is locally quasi finite`: eight scheme hits (LocallyQuasiFinite,
  constructors, finite/immersion instances, quasi-separated diagonals); no match.
- rg on project WeilConjectures and Sheaf, by
  `relative.*[Dd]iagonal|[Rr]elativeDiagonal|moduli.*[Dd]iagonal|SpaceMapIsLocallyQuasiFinite`:
  found existing `moduliRelativeDiagonal`, `ModuliSpaceTest` and other morphism
  definitions in DmStackMorphismProperties, which are reused. Other hits concern
  scheme diagonals, unramified-diagonal/atlas criteria, open substacks or
  composition/calculus and are not this theorem. A precise search for
  `ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite (moduliRelativeDiagonal`
  found only the defining condition in IsLocallyQuasiFiniteModuliMap, not a
  theorem for arbitrary f. Searches for the chosen declaration name in Mathlib,
  WeilConjectures, Sheaf and dag/lean_names_upstream.json found no clash.
- `grep -rn lem-sfb-dm-relative-diagonal-quasifinite lean/WeilConjectures`:
  no hits. No exact existing statement was found.

Validation: prescribed scompile.py compiled the sandbox statement and the library
module cleanly (3.3 s and 3.2 s respectively), with no errors or unexpected
warnings. All variables and universes are explicitly bound and autoImplicit is
disabled. The delivery contains one theorem with the expected sorry proof.
The latest blueprint direct-images statement and proof (3) were read; this
auxiliary stack lemma does not change that blueprint statement or route.

## Second reading by Q123

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
