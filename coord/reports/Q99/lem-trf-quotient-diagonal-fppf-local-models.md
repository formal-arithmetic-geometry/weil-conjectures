## Worker report

The delivery states `AlgebraicGeometry.Scheme.quotient_diagonal_fppf_local_models`
in `Sheaf.AlgebraicGeometry.QuotientDiagonalFppfLocalModels`. Its only postponed
proof is that theorem. The supporting definition `quotientDiagonalFibre` constructs
the relative diagonal fibre explicitly, as a subtype of `PUnit` cut out by equality
of the two restricted sections. Its restriction maps use the naturality of those
sections. There is no chosen unknown object or postponed definition data.

I read the complete item, its statement dependencies and their recorded signatures,
and Stacks `spaces.tex`, Tag 0265, the third representability step and its square and
cube (lines 1556–1601 in this snapshot). The node obtains a common fppf refinement
directly from local sections of sheafification, rather than invoking representability
of the quotient map first. The theorem follows the node's stated generality: no
hypothesis of affineness of U or separatedness of S is introduced.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Scheme S, S-schemes R and U | `{S : Scheme.{u}} {R U : Over S}` |
| The map j=(s,t) to U times_S U is a monomorphism | `(s t : R ⟶ U) [Mono (prod.lift s t)]`; products in `Over S` are the relative scheme products |
| Equivalence relation on every U(W) | `hrel`, quantifying over all `W : Over S`, with relation `∃ r, r ≫ s = b ∧ r ≫ t = c` |
| Both projections are etale | `[Etale s.left] [Etale t.left]` |
| Big fppf site over S | `Scheme.fppfTopology.over S` |
| Sheafification F of the pointwise quotient | `F : Sheaf ... (Type u)`, its unit `η` from the presheaf coequalizer, and `hη`, the sheafification universal property |
| Canonical quotient map q | `coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η` |
| The stated size convention | Explicit `universe u`; schemes in `Scheme.{u}`, hom sets and sheaf values in `Type u`, covering indices in `Type (u + 1)` |
| j separated | `[IsSeparated (prod.lift s t).left]` |
| j locally quasi-finite | `hj : Scheme.Hom.IsLocallyQuasiFinite (prod.lift s t).left`, retaining the Stacks finite-type requirement |
| Every T and every pair of maps from h_T | `(T : Over S) (a₁ a₂ : yoneda.obj T ⟶ F.obj)` |
| Relative diagonal fibre H | `quotientDiagonalFibre T F a₁ a₂` on `(Over T.left)ᵒᵖ` |
| H is a sheaf of sets | First conjunct `Presheaf.IsSheaf (Scheme.fppfTopology.over T.left) ...` |
| Singleton exactly for equality, empty otherwise | The second conjunct, for every `W : Over T.left`, states `Subsingleton H(W)` and `Nonempty H(W) ↔ a₁(W)(W.hom) = a₂(W)(W.hom)` |
| A common fppf covering | Existential `I`, `Tᵢ`, `f`, and membership of their underlying family in `Scheme.fppfPrecoverage T.left` |
| Local lifts u_i and v_i | The two families `uᵢ vᵢ : ∀ i, Tᵢ i ⟶ U` |
| Both required lifting equalities | Separate `∀ i` equalities of natural transformations, composing each local lift with q and each covering map with the corresponding a |
| Specified local schemes Y_i | `pullback (prod.lift (uᵢ i) (vᵢ i)).left (prod.lift s t).left` |
| Their structure maps to T_i | The corresponding `pullback.fst`, the projection to the first factor T_i |
| Natural identifications H restricted to T_i with h_Y_i | The `Nonempty (... ≅ yoneda.obj (Over.mk (pullback.fst ...)))` conjunct; the left side restricts along `(Over.map (f i).left).op` |
| Every Y_i to T_i separated and locally quasi-finite | Final conjunct, using `IsSeparated` and the same `Scheme.Hom.IsLocallyQuasiFinite` as in the hypothesis |

The fibre definition does not replace the diagonal by an arbitrary subterminal
presheaf: its sections are exactly the equality witnesses at the specified map
`W → T`. The displayed presheaf fibre product has elements `(w,x)` with
`a₁(w)=x=a₂(w)`. Fixing w to the slice structure map eliminates the uniquely
determined x and gives precisely this subtype of `PUnit`. Naturality supplies
precomposition. Thus this is a concrete realization of the node's canonical H,
with no extra assumption on H and no change of the node statement.

The coequalizer/sheafification interface is the one already used by
`Sheaf.AlgebraicGeometry.EtaleRelationKernelPair`. Since the sectionwise relation
is an equivalence relation, the pointwise coequalizer is U(W)/R(W). The bijectivity
of precomposition with η against every sheaf is exactly the sheafification universal
property. It avoids imposing a sheafification functor for every small-valued
presheaf on a big site, an additional hypothesis the node does not make.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (also exported by
  `Mathlib.AlgebraicGeometry.Pullbacks`): `pullback`, `pullback.fst`; the scheme
  pullbacks and the products of `Over S` give the specified relative geometry.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology` and
  `Scheme.fppfPrecoverage`; `Mathlib.CategoryTheory.Sites.Over` supplies
  `GrothendieckTopology.over`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  and `sheafificationAdjunction` specify the universal property represented by hη.
- `def-weil-size-convention` is a convention record with no declaration; it is
  implemented by explicit universe levels, with no equality imposed between
  the site's object and morphism universes.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the exported
  `AlgebraicGeometry.IsSeparated`, whose diagonal is a closed immersion.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, with
  `IsQuasiFiniteAtPoint` and its finite-type condition read in the source.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; sheaf and topology notions
  retain their Mathlib meanings as its record says.

Proof-dependency modules are imported without `public`:
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`,
`Sheaf.AlgebraicGeometry.EtaleRelationKernelPair`, and
`WeilConjectures.AlgebraicGeometry.SeparatedLqfBaseChange`. The other proof
inputs are already public statement dependencies. The docstring gives all five
proof steps and their DAG citations.

Edge cases checked before writing:

- Empty test schemes and empty covers: the sheaf F has one section on an object
  admitting an empty cover, so the equality fibre is a singleton there. The
  covering index type is not assumed nonempty.
- Empty relation and empty U: no representative is demanded over a nonempty
  test scheme unless the given section exists; local covers handle empty objects.
- Equal maps a₁=a₂: H is the terminal relative sheaf and the local model is the
  base change of the relation along the pair of local lifts, with no removed case.
- Unequal restricted sections: the equality subtype is empty, as required.
- Arbitrary bases and nonaffine U: there is no affineness, no quasi-compactness,
  no finite-type condition on T, and no separatedness condition on S.
- Scheme size is u+1 and morphism size u. The cover index can have size u+1,
  so the presieve-sized cover and successive common refinements are allowed.

Searches for an existing statement (all on 2026-10-22):

- `msearch.py`, LeanFinder: “Local fppf lifts of two sections of a quotient sheaf
  identify its diagonal fibre with the pullback of the equivalence relation”.
  Eight hits: `Scheme.Pullback.diagonalRestrictIsoDiagonal`, `Meq.pullback`,
  `Scheme.LocalRepresentability.glueData_t'`, `SheafOfModules.Presentation.map_π_eq`,
  `Scheme.Pullback.diagonalCover_map`, `Meq.pullback_apply`,
  `GrothendieckTopology.Point.toPresheafFiber_eq_iff'`, and
  `ExistsHomHomCompEqCompAux.g`; none states this result.
- `msearch.py`, LeanSearch: “The diagonal fibre of a quotient sheaf is locally
  represented by the pullback of the equivalence relation”. Eight hits about set
  pullback diagonals, `Setoid.comap_eq`, morphism-property diagonals, and Galois
  fibre pullback equivalences; none is a quotient-sheaf local-model theorem.
- `msearch.py`, Loogle: `CategoryTheory.Limits.equalizer, CategoryTheory.yoneda`:
  no hits.
- `msearch.py`, Mathlib grep in `AlgebraicGeometry`:
  `quotient.*diagonal|diagonal.*quotient`: no hits.
- `rg` in the upstream and project algebraic-geometry source for quotient
  diagonals, equivalence relations, and quotient presheaves found
  `EtaleRelationKernelPair`, `EtaleAffineQuotientRepresentable`, and
  `EtaleRelationRestrictionQuotient`. Their full signatures were read. The first
  gives the kernel-pair input; the second assumes U affine and states global
  representability; the third concerns restricting a relation. None states this
  item's simultaneous-cover and specified-diagonal-model conclusion.
- Exact item-id search in `lean/WeilConjectures` and `lean/Sheaf`: no match.
  Exact declaration-name search in Mathlib, upstream source, project source, and
  `dag/lean_names_upstream.json`: no match.

There are no new nodes, dependency repairs, or statement corrections. Only the
item's `lean` field is changed. The earlier stage-1 “already split and reviewed
under Q71” refusal does not prevent adding the missing stage-2 Lean statement
using the prescribed stage-2 delivery tool.

## Second reading by Q99

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
