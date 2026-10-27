## Worker report

The module `Sheaf.AlgebraicGeometry.PointedDevissageEtaleRefinement` states
`AlgebraicGeometry.PointedAffineOneStep.exists_elementaryEtale_refinement`.
There is one theorem, with `sorry`; no new definitions, dependency repairs, statement
corrections or additional axioms. The item node changes only in `lean`.

Sources read: Stacks `flat.tex`, Tag 05HE,
`lemma-elementary-etale-neighbourhood` (lines 1027–1148), including the diagram,
the cartesian ambient lift, and the geometric-irreducibility refinement; Tag 05HR,
`proposition-existence-complete-at-x` (lines 1429–1550), particularly the pullback
of the first alpha and its cokernel. The auxiliary definition explicitly omits the
support-dimension equalities, so the proof uses the datum's given fibre dimension d.
The current blueprint ancestor `lem-trf-local-term-locality.md` and its proof under
`literature/blueprint/latest/` were also read: this is historical supporting algebra,
not a replacement statement for that unit. There is no repair note for this item.
The example CompactObject module is now withdrawn; its node points to the upstream
`WeilConjectures.CategoryTheory.CompactObject` declaration. Module mode, explicit
universes, public statement imports and private proof imports follow current rules.

Hypothesis-by-hypothesis and clause-by-clause translation:

- `X B : Scheme.{u}`, `f : X ⟶ B`, `F : X.Modules`, `x : X`, and
  `s : PointedAffineOneStep f F x` are precisely the input pointed affine datum;
  b is `f x`. The dependency structure includes local finite type of f, finite-type
  quasi-coherence of F and G, affineness of X,B,Z,Y, the two B-maps, their commuting
  triangle, closed immersion of finite presentation, finite pi, smoothness, geometric
  irreducibility, dimension `s.d`, the presentation, the marked incidences, singleton
  fibre, and purely transcendental marked residue extension. No support-dimension
  equality is introduced.
- `g' : Y' ⟶ B'`, `aY : Y' ⟶ s.Y`, `aB : B' ⟶ B`, `y'`, `b'`,
  `square : aY ≫ s.g = g' ≫ aB`, `marked : g' y' = b'` encode the square
  of pointed schemes. `targetElementary` and `baseElementary` are exactly the
  elementary étale hypotheses, including the point equations and invertibility
  of the induced residue-field maps. Neither Y' nor B' is assumed affine.
- The existential `B''`, `cB : B'' ⟶ B'`, `b''`, `IsAffine B''`, and
  `IsElementaryEtalePointed cB b'' b'` give the affine elementary neighbourhood.
  `IsElementaryEtalePointed (cB ≫ aB) b'' (f x)` explicitly records its
  elementary composite to the original base, hence the stated kappa(b'')=kappa(b)
  via the actual induced map. Here “affine map” means affine neighbourhood/source,
  as in the source's first paragraph; it does not assume B' is affine.
- `X''`, `aX`, `f''`, `x''`, the elementary condition on `aX`,
  `f'' x'' = b''`, and `aX ≫ f = f'' ≫ cB ≫ aB` give the pointed ambient
  map over the prescribed composite base map. Affineness of X'' is in `t.affineX`.
- `t : PointedAffineOneStep f'' ((tensorPullback aX).obj F) x''` is the new
  datum for the actual tensor pullback F''. All its smoothness, fibre dimensions,
  geometric irreducibility, finiteness, singleton fibre, affineness and closed
  finite-presentation immersion conditions are those of the dependency, not a
  duplicate definition. `t.d = s.d` retains exactly the same relative dimension.
- `j : t.Y ⟶ pullback g' cB` and `IsOpenImmersion j` identify the affine
  scheme `t.Y` with an affine open of Y' x_{B'} B''. Describing an open subscheme
  by an open immersion is equivalent to naming an open subset; no extra target
  is permitted. `j ≫ pullback.snd g' cB = t.g` fixes its structure map.
  `(j ≫ pullback.fst g' cB) t.y = y'`, together with `t.markedBase` and
  `f'' x'' = b''`, makes its marked point lie over the distinguished pair
  (y',b''). Thus the affine open contains the required point.
- `h : t.Y ⟶ s.Y` is fixed by
  `j ≫ pullback.fst g' cB ≫ aY = h`.
  `IsElementaryEtalePointed h t.y s.y` gives its marked incidence and the
  specified induced isomorphism kappa(y) -> kappa(y'').
- `e : t.Z ⟶ s.Z`, `e t.z = s.z`, and
  `finiteSquare : IsPullback e t.π s.π h` make Z'' precisely the cartesian
  base change of Z along h, with the actual pulled-back pi and marked point.
  A general cartesian model, canonically isomorphic to the chosen `pullback`,
  avoids transports of modules across arbitrary definitional equalities.
- `closedSquare : IsPullback e t.i s.i aX` is exactly the additional
  cartesian square of i'',i,aX,e required by the node.
- `eG : (tensorPullback e).obj s.G ≅ t.G` identifies G'' with the actual
  pullback of G. The first equality after eG pins `t.presentation` to the
  pullback of `s.presentation` using the canonical base-change map for i;
  merely asserting existence of an unrelated presentation would lose that data.
- `β` is the required isomorphism h^*(pi_*G) ≅ pi''_*G''. Its hom is pinned
  to `moduleBaseChangeMap s.π t.π h e finiteSquare.w s.G`, followed only by
  pushforward of the supplied identification eG. Thus this is the canonical
  comparison, not an arbitrarily chosen isomorphism between the same objects.
- `r : ℕ` allows all finite ranks, including zero. `α` has exactly the
  source `free (ULift (Fin r))`, i.e. O_Y^{direct-sum r}, and target pi_*G.
  The antecedent using `IsResidueFibreIso` at each generic point of
  `s.g.fiber (f x)` is precisely the residue-field isomorphism hypothesis.
  This fibre is nonempty and irreducible by s, so this is equivalent to the
  assertion at its unique generic point, viewed in Y using `fiberι`.
- `α''` is pinned by its equality to the inverse of the canonical free-module
  pullback isomorphism, followed by `(tensorPullback h).map α ≫ β.hom`.
  Hence it is exactly the pulled-back alpha with the displayed target, not a
  newly chosen generic basis. Its `IsResidueFibreIso` clause at every generic
  point of `t.g.fiber b''` is precisely preservation of the generic property.
- `q : (tensorPullback h).obj (cokernel α) ≅ cokernel α''` states the
  cokernel identity up to canonical isomorphism. The final equality with
  `(tensorPullback h).map (cokernel.π α)` and `β.hom ≫ cokernel.π α''`
  retains the quotient map, and fixes the canonical identification.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.PointedAffineDevissage`:
  `AlgebraicGeometry.PointedAffineOneStep`, `IsElementaryEtalePointed`,
  `IsResidueFibreIso`, and their full signatures and docstrings were read.
  All belong to the sole statement dependency
  `def-trf-pointed-scheme-devissage-data`; its recorded module is publicly imported.
- `WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`:
  `AlgebraicGeometry.Scheme.Modules.moduleBaseChangeMap`, the adjunction mate
  defined with the actual tensor pullback and the composite-pushforward comparison.
- `WeilConjectures.AlgebraicGeometry.PicardTensorFrameCoordinates`:
  `AlgebraicGeometry.Scheme.Modules.picardTensorFrameUnitIso` and
  `picardTensorFreeIso`. The latter is the existing mapFreeIso comparison
  normalized on each summand by tensorPullbackObjUnitToUnit; it is used directly.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction` and
  `WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`:
  tensorPullbackSectionAdjunction, tensorPullbackSectionComp,
  tensorPullbackObjUnitToUnit and tensorPullbackObjUnitToUnit_isIso were read to
  check the canonical normalization of these comparisons.
- Existing recorded proof dependency modules are imported without `public`, including
  finite-type residue transcendence degree, module pullback finiteness and
  quasi-coherence, affinePushforward_baseChange, stalk pullback, quasi-coherent
  cokernel/image, affine pullback sections and dimension_locally_algebraic.
  No statement is invented for the currently unstated proof dependency
  `lem-trf-finite-smooth-integral-base-refinement`; it is not needed to type this
  theorem. The theorem docstring carries all ten DAG proof steps.

Edge cases checked before writing:

- The marked points force the relevant schemes and marked fibres to be nonempty;
  no extra Nonempty assumptions are added. The original smooth map's other fibres
  satisfy the dependency's geometric-irreducibility convention.
- d=0 is allowed and retained. The Spec(k) identity datum is the elementary test.
- r=0 is allowed: the free sheaf is zero, and the antecedent requires the target
  residue vector space to be zero. Pullback of this map and its cokernel is still
  covered. F=0 and G=0 are allowed; no support dimension is used.
- Identity maps on both sides of the input square are allowed, as are non-affine
  elementary input neighbourhoods; only the resulting affine neighbourhoods are
  required affine. Empty input neighbourhoods cannot carry y' or b'.
- The quantification over all generic points does not become vacuous: geometric
  irreducibility gives nonempty irreducible fibres, which have generic points.
- One explicit universe u is inherited from the recorded Scheme/modules interface;
  no extra universe equality or smallness assumption is imposed. `ULift.{u}` keeps
  the finite free index in the module universe without excluding r=0.

Searches actually run:

1. `msearch.py ... leanfinder` query “Refine a pointed affine scheme devissage
   along elementary etale target and base maps preserving finite pushforward and
   generic fibre bases”: 8 hits about étale/smooth morphisms and residue fields,
   none stating this refinement theorem.
2. `msearch.py ... loogle '"devissage"'`: 0 hits.
3. `msearch.py ... grep 'devissage|Devissage|ElementaryEtale'`: 0 Mathlib hits.
4. `msearch.py ... leansearch` query “An elementary etale refinement of a pointed
   one step devissage preserves generic residue field bases and cokernels”:
   8 hits on ring/scheme étaleness and algebraic étale neighbourhoods; no match.
5. `rg` on upstream WeilConjectures and project Sheaf for devissage, Devissage,
   ElementaryEtale: existing pointed data and numerous unrelated devissage
   statements; no theorem with these clauses. `grep -rn` for the exact item id
   on WeilConjectures: no hits. `rg` for the exact theorem name/item id in
   Sheaf, WeilConjectures and `dag/lean_names_upstream.json`: no hits.
6. Targeted `rg` for moduleBaseChangeMap and tensorPullback/free comparisons
   found the upstream canonical map and `picardTensorFreeIso`; both were opened
   and reused. No helper definition node is needed.

Validation: `scompile.py ND lem-trf-devissage-pointed-etale-refinement` compiled
both sandbox and library module modes cleanly (4.2s and 2.8s). A first compile
identified an unnecessary `open Scheme.Modules` before the namespace and a
closing-docstring whitespace warning; both were removed. Final dry-run and
push results are recorded below after execution.

## Second reading by ND

This is a second author reading, not an independent agent review: the dispatcher
explicitly prohibits starting other agents. The maintainer's independent reading
follows delivery. With the JSON statement and complete Lean file open, I checked
all input hypotheses, then the conclusion in its original order.

The affine open is expressed via the open immersion j; t.affineY and the two
projection equations give exactly the desired affine open over B''. Its marked
point maps to y' and b'', rather than only to their images in Y and B. The new
one-step record is on the actual tensor pullback of F. The finite and closed
cartesian squares share the same e, and the G identification uses that e.
The presentation equality retains the original presentation. The equality for
beta prevents an arbitrary replacement of finite-pushforward base change.
The alpha equality fixes both its source free-module identification and its
pushforward target. The generic test is on the actual old and new marked fibres,
and the quotient equality fixes the cokernel isomorphism. Composite elementary
base and target conditions express the induced residue-field isomorphisms.
No source clause or edge case was dropped, and no counterexample or statement
fault was found. No mathematical changes were needed on this second reading.

Final dry run: `deliver2.py ND lem-trf-devissage-pointed-etale-refinement --no-push`
printed `OK (dry run): commit e0fea62383a passes the preflight and compiles; nothing
pushed`. Its local compiler encountered `OSError(28, 'No space left on device')`;
the wrapper automatically confirmed against current server sources and passed.
The final source has 223 lines, no line over 100 characters, and both implicit
binding options disabled. JSON comparison confirms only `lean` changed.
