## Worker report

Repair of returned head b3e61ddc3666, addressing H4 and H3. The delivery now reuses
`CategoryTheory.PreGaloisCategory.IsGalois` from
`Mathlib.CategoryTheory.Galois.GaloisObjects` (`existing: true`, branch `mathlib`).
The duplicate `Sheaf.AlgebraicGeometry.FundamentalGroup.IsGaloisCover` module was removed.
The node changes only in `lean`; its source statement and dependencies are unchanged.
The earlier second-reading section was removed because it endorsed the returned version;
the repaired record needs the dispatcher's fresh second reading.

Source read: blueprint sec-smooth-purity/sk-prop-a1-kummer/def-galois-object.md,
node order 1901. The existing class is intrinsically independent of a choice of geometric
point, and its specialization is exactly the stated notion, as follows.

Clause-by-clause correspondence:

- Connected base: specialize to `{Y : Scheme.{u}} [ConnectedSpace Y]`.
  `AlgebraicGeometry.Scheme.FiniteEtale.galoisCategory` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic` supplies the required
  `GaloisCategory Y.FiniteEtale` instance. This is available for every connected scheme,
  with no Noetherian, finiteness, smoothness, or characteristic condition.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`
  and `s : Spec (.of Ω) ⟶ Y`. In particular the hypothesis is algebraic closedness,
  not merely separable closedness. The latter is inferred for use of the existing fibre
  machinery. The intrinsic predicate has no point parameter because the characterization
  below holds at every such point.
- Finite étale `P → Y`: specialize `IsGalois` to `(P : Y.FiniteEtale)`, the recorded
  finite-étale category from `def-galois-categories`. Its arrows are precisely Y-morphisms,
  so `Aut P` is the full group `Aut_Y(P)`.
- Connected source: `IsGalois` extends `PreGaloisCategory.IsConnected P`. This is equivalent
  to `ConnectedSpace P.obj.left` by the existing two declarations
  `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_of_connectedSpace` and
  `AlgebraicGeometry.Scheme.FiniteEtale.connectedSpace_of_isConnected`, in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected`.
- Simple transitivity: `AlgebraicGeometry.Scheme.FiniteEtale.isGalois_iff s P`, in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`, states exactly
  `IsGalois P ↔ IsConnected P ∧ ∀ x : (fiber s).obj P,
  Function.Bijective (fun σ : Aut P ↦ (fiber s).map σ.hom x)`.
  Bijective evaluation at each x says every endpoint is reached by exactly one
  automorphism. `fiber_map_left` identifies this map with postcomposition by the underlying
  Y-automorphism. Thus the quotient-based definition of IsGalois is already equivalent to
  both clauses in the node; a scheme-specific second predicate is unnecessary.

Dependency declarations read, including signatures and docstrings:

- `def-galois-categories`: `AlgebraicGeometry.Scheme.FLC`, module
  `Sheaf.AlgebraicGeometry.GaloisCategories`. Its note assigns the finite-étale clause to
  `AlgebraicGeometry.Scheme.FiniteEtale`, module
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`. That is the clause used
  here; FLC is not needed for this finite-étale definition.
- `def-galois-fibre-functor`: `AlgebraicGeometry.Scheme.FiniteEtale.fiber` in the same upstream
  FiniteEtale module. It sends P to the finite set of Y-morphisms Spec Ω → P and arrows to
  postcomposition. Its signature accepts separably closed fields, hence also the
  algebraically closed fields required for the geometric point in this node.
- The IsGalois class and its `autMulFiber` action were read in Mathlib's GaloisObjects.
  The complete upstream `isGalois_iff` characterization and both connectedness bridges
  were read, rather than dismissing them because their definitions are abstract.

Edge cases checked: the empty cover is excluded by connectedness (IsConnected is
noninitial), even though evaluation on an empty fibre alone is vacuous. The identity
cover is connected and its singleton fibre has the required bijective evaluation.
Disconnected covers are excluded. A connected non-Galois cover fails bijective evaluation.
The empty base cannot satisfy ConnectedSpace or admit the stated geometric point.
No chosen fibre element, degree restriction, or extra structure on P is introduced.
The scheme and point universes follow the existing fibre interface and u is arbitrary.

Searches (group ND, item def-galois-object):

- LeanFinder, repair query `connected finite etale cover automorphism group simply transitive
  geometric fibre IsGalois`: 8 hits, including `isGalois_iff_pretransitive`, confirming the
  existing abstract predicate that specializes to this notion.
- Loogle, repair query `CategoryTheory.PreGaloisCategory.IsGalois`: 12 hits, including the
  class in `Mathlib.CategoryTheory.Galois.GaloisObjects` and its evaluation equivalence.
- msearch grep, repair query `class IsGalois` under `CategoryTheory/Galois`: exact class at
  GaloisObjects.lean:46.
- Original LeanSearch query `Galois cover of a connected scheme with simply transitive action
  on its geometric fiber`: service returned Internal Server Error. This failure does not
  negate the exact class and characterization found by the other searches.
- Source rg `IsGalois`, `isConnected`, `connectedSpace`, and `def-galois-object` found and
  was followed by reading FundamentalGroup/Basic.lean and Connected.lean. Project rg and
  Mathlib searches from the original attempt were reconsidered: their abstract hits DO
  apply after specialization, contrary to the returned report's conclusion.

Validation: a scratch probe compiled cleanly using scompile.py on the server (1.7 s,
 nice 19, two threads, 60-second per-file limit). It checked the existing class, its
specialization to Y.FiniteEtale, `isGalois_iff s P` under `[IsAlgClosed Ω]`, and both
connectedness bridges. There is no delivered Lean module, no new definition, no new node,
no dependency module, no statement correction, and no disputed statement.

## Second reading by ND

I read the source node (blueprint `sec-smooth-purity/sk-prop-a1-kummer/def-galois-object.md`, order 1901), its dependency nodes, and the recorded Lean declaration. The node introduces: (1) a connected scheme `Y` with a geometric point `\bar y`; (2) a finite étale cover `P → Y`, namely an object of `F Et(Y)`; and (3) the predicate that `P` is connected over `Y` and that `Aut_Y(P)` acts simply transitively on the geometric fibre `P_{\bar y}`. The node has no additional finiteness, Noetherian, smoothness, characteristic, or degree hypotheses.

The Lean record is `CategoryTheory.PreGaloisCategory.IsGalois` in `Mathlib.CategoryTheory.Galois.GaloisObjects`, with signature `class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C) : Prop extends IsConnected X`. Specializing `C` to `Y.FiniteEtale` uses the recorded `galoisCategory` instance for connected `Y`; `X` is exactly the finite étale object `P`, so its automorphisms are precisely `Aut_Y(P)`. The inherited `IsConnected X` is identified with connectedness of the source scheme by `FiniteEtale.isConnected_of_connectedSpace` and `connectedSpace_of_isConnected`. The recorded theorem `FiniteEtale.isGalois_iff s P` identifies `IsGalois P` with connectedness together with bijective evaluation of every automorphism on every point of the fibre of the geometric point `s`; bijectivity is exactly simple transitivity. Thus the existing predicate renders every conclusion clause without adding hypotheses or dropping the geometric-point characterization.

The geometric point is represented in the existing fibre interface by `s : Spec (.of Ω) ⟶ Y` with `[Field Ω] [IsAlgClosed Ω]`; the universe is shared with `Y`, and no case is excluded. Empty or disconnected covers fail the inherited connectedness clause; the identity cover satisfies it and has singleton fibre. The empty base is excluded exactly when the source node's connectedness and geometric-point hypotheses are unavailable. No separate chosen fibre element or degree assumption is introduced.

I searched Mathlib and the source repository using LeanFinder, Loogle, `msearch.py`, and `rg`. The only relevant declaration is the abstract `PreGaloisCategory.IsGalois` and its `isGalois_iff_pretransitive` characterization; no scheme-specific duplicate exists. The prior duplicate `Sheaf.AlgebraicGeometry.FundamentalGroup.IsGaloisCover` was therefore correctly removed. I found no mismatch in the node statement or its dependency records, and made no further changes in this second reading.
