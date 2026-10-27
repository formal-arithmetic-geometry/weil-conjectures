## Worker report

Module `Sheaf.AlgebraicGeometry.SpaceDescendClosedImmersion` states
`AlgebraicGeometry.AlgebraicSpace.exists_isClosedImmersion_affine_stage`, with its
single theorem proof postponed by `sorry`. No definitions or auxiliary theorems are added.
The statement is unchanged. The only additional statement dependencies are the three
already landed owners of the qcqs and local chart predicates used below.

Source checked: `literature/stacks-project/spaces-limits.tex`, lines 1449–1456
(Situation 084W, `situation-descent-property`) and lines 1670–1689 (Tag 0850,
`lemma-descend-closed-immersion`, statement and proof). The source assumes qcqs for
B₀, X₀ and Y₀; here B₀ is affine and hence automatically qcqs. Its two further
hypotheses are exactly local finite type of h₀ and closed immersion of h.

Clause-by-clause rendering:

- Work over Spec Z in the chosen scheme universe: the base throughout is
  `Spec (.of (ULift.{u} ℤ))`. ULift puts the integer ring in universe u; it does not
  change the base scheme mathematically. `universe u` and every variable are explicit,
  and `set_option autoImplicit false` forbids auto-bound variables.
- A small nonempty directed set I: `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. The project uses preorders for directed sets. I is in the
  scheme universe, as required by the size convention for elementwise limits.
- The inverse system of affine schemes: `D : Iᵒᵖ ⥤ Over (Spec (.of (ULift.{u} ℤ)))`;
  `haff` says `IsAffine (D.obj i).left` at every index. `htransition` says every
  `(D.map a).left` is an `IsAffineHom`. All morphisms are maps over Spec Z.
- T and its limit projections: `c : Cone D` and `hc : IsLimit c`. Its scheme is
  `c.pt.left` and its projection to Tᵢ₀ is `(c.π.app (op i₀)).left`. Limits in the
  slice of schemes are the scheme limits with their structure maps: forgetting the
  slice creates these connected limits. No limit over a different base is used.
- Fix a stage: `i₀ : I`.
- The two qcqs spaces and the map over that stage: `U₀ V₀ : AlgebraicSpace` over
  Spec Z, `h₀ : U₀ ⟶ V₀`, and `v₀ : V₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀))`.
  The structural map of U₀ is `h₀.hom.hom ≫ v₀`. Thus giving these data is exactly
  giving a Tᵢ₀-map, with no free unrelated structural morphism or missing equation.
  Yoneda identifies scheme maps with maps of their represented presheaves.
- Quasi-compactness of each space is `hUqc : IsQuasiCompact U₀.obj` and
  `hVqc : IsQuasiCompact V₀.obj`. The existing predicate is existence of a
  representable surjective étale atlas from a `CompactSpace` scheme, exactly the
  node's convention; it does not assume the spaces themselves are schemes.
- Quasi-separatedness of each space is `hUqs : IsAbsolutelyQuasiSeparated U₀` and
  `hVqs : IsAbsolutelyQuasiSeparated V₀`. This existing predicate is the equivalent
  affine-pair test for quasi-compactness of the absolute diagonal. Over Spec Z this
  is precisely the node's structure-morphism quasi-separatedness. The affine-test
  and all-quasi-compact-space-test conventions agree (Stacks 03HE and 0AHR).
- Local finite type on étale scheme charts is
  `hlft : MapIsLocally (@LocallyOfFiniteType) h₀`, the existing all-compatible-chart
  predicate with Mathlib's scheme notion; no finite presentation hypothesis is added.
- U, V and h are the actual presheaf pullbacks along
  `yoneda.map (c.π.app (op i₀))`: `Over.pullback ...` acts on the slice morphism
  `Over.homMk (U := Over.mk (h₀.hom.hom ≫ v₀)) (V := Over.mk v₀) h₀.hom.hom rfl`.
  Its `.left` is precisely the induced map U→V. Presheaf pullbacks of sheaves
  compute sheaf fibre products; the recorded fibre-product closure theorem supplies
  algebraic spaces. This is a canonical functor, not an arbitrary comparison map.
- The limit closed-immersion assumption is `hclosed : IsRepresentableWith
  (fun _ _ p ↦ IsClosedImmersion p.left) ...` for this exact map. By definition this
  says every scheme test has a representing pullback scheme and its projection is
  a closed immersion. The property is invariant under the unique isomorphism of
  representing schemes, so existential representing squares express every test.
- The conclusion is `∃ (i : I) (hi : i₀ ≤ i), IsRepresentableWith ...` for the
  pullback of the same slice map along `yoneda.map (D.map (homOfLE hi).op)`.
  Contravariance gives Tᵢ→Tᵢ₀. This is exactly hᵢ and exactly the existence of a
  closed-immersion stage; no assertion of eventuality has been added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, and `Spec.map` (the scheme and affine-spectrum leaves).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicSpace.IsRepresentableWith`; the latter is quantified over all scheme
  tests and uses an actual `IsPullback` square. Imported through the recorded
  fibre-product module and the owning predicate modules.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`, all in `AlgebraicGeometry.AlgebraicSpace`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, used inside the existing atlas
  predicate. `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.StackQcqsMorphism`:
  `AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact` (owning node
  `def-sfb-stack-qcqs-morphism`, added to stmt_deps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated`:
  `AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated` (owning node
  `def-sfb-space-absolute-quasi-separated`, added to stmt_deps).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` (owning node
  `def-sfb-space-morphism-properties`, added to stmt_deps).
- Mathlib `Over.pullback`, `Over.homMk`, `homOfLE`, `Cone`, and `IsLimit` provide
  the canonical category-theoretic data; no project copy is introduced.

Proof imports include the recorded modules
`WeilConjectures.AlgebraicGeometry.LimitAffineTransition` and
`WeilConjectures.AlgebraicGeometry.DescendClosedImmersion`, as well as the Mathlib
modules for affine permanence, affine qcqs, and closed-immersion base change.
The other proof-dependency nodes have no Lean record or Mathlib match in the read
checkout; no nonexistent module is imported. The five proof steps in the docstring
retain every cited node and the argument in the accepted split.

Edge cases checked before writing: I cannot be empty, and i=i₀ is allowed through
reflexivity; singleton and constant systems are included. A directed preorder need
not be antisymmetric. Empty affine bases (zero coordinate ring), empty source or
empty target spaces, and an empty limit are allowed; neither Nonempty on schemes
nor a field/nontriviality/Noetherian hypothesis is imposed. U₀ and V₀ are not
required to be representable; representability is part of the closed-immersion
condition only. The limit maps need not be surjective. The size convention uses
one explicit universe for schemes and the small index type.

Searches made for existing statements and notions:

- `msearch.py` LeanFinder, query “Closed immersions of algebraic spaces descend
  along directed inverse limits of affine schemes”: 8 hits, all scheme results,
  chiefly `exists_mem_of_isClosed_of_nonempty` and scheme finite-type Hom descent;
  none states algebraic-space closed-immersion descent.
- `msearch.py` Loogle, query `"IsClosedImmersion", "IsLimit"`: 0 hits.
- `msearch.py` grep, query `descend.*closed|closed.*[Ll]imit|AlgebraicSpace`,
  subdirectory `AlgebraicGeometry`: 11 hits, scheme finite-limit/property code and
  universally closed fpqc descent; no algebraic-space limit-descent result.
- `msearch.py` LeanSearch, query “A morphism of algebraic spaces locally of finite
  type which is a closed immersion after an affine inverse limit base change is a
  closed immersion at some stage”: 8 scheme-property hits, including
  `IsClosedImmersion`, `isClosedImmersion_iff_isAffineHom`, and base-change stability;
  none states this lemma.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, by the item id and by
  `descend.*closed`, `ClosedImmersion`, `IsQuasiCompact`, `QuasiSeparated`,
  `LocallyOfFiniteType`, and `AlgebraicSpace`: found the existing predicate modules
  reused above and scheme descent in `DescendClosedImmersion`; no existing exact
  algebraic-space theorem. `dag/lean_names_upstream.json` also has the Nagata
  scheme-stage result, not this algebraic-space statement. The full signatures
  and docstrings of the predicate modules and recorded dependencies were read.

No new nodes, dependency repairs, statement correction, or statement dispute.

Validation: `scompile.py NC lem-sfb-space-descend-closed-immersion` compiled the
module against the live server build in both sandbox and library module modes,
3.9 seconds each, with no errors or warnings. `deliver2.py --no-push` passed the server preflight and compilation
(OK, dry-run commit 80bb4f4cf13).

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
