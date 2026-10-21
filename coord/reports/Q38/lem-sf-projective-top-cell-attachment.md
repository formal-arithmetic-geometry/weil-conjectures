## Worker report

The module `Sheaf.Paper.ProjectiveTopCellAttachment` states
`CochainComplex.projective_top_cell_attachment`. Its only theorem has proof `sorry`.
There are no new definitions, dependency repairs, or statement changes. The node copy
changes only `lean`.

The source was read in `literature/stacks-project/proetale.tex`, Tag 09C3,
`lemma-local-structure-constructible-complex`, especially its final paragraph: the
connecting morphism gives a map from the last term, extends the complex by one, and
represents the original object. The general projective-source representative is
`derived.tex`, Tag 064B, `lemma-morphisms-from-projective-complex`. The cone convention
was checked in `derived.tex`, Tag 014E, `definition-cone`, against Mathlib's mapping
cone and cochain shift. The provided node already spells out the expanded argument.

Hypotheses, one by one:

- The site small relative to the module universe is `{C : Type u} [SmallCategory C]`
  with `J : GrothendieckTopology C`. The integer and module universes are explicit;
  there is no assumption on the number of site objects or a terminal object. As in
  the dependency's Mathlib interface, the ring and module universe is `u`; small
  rings and sites may be placed in this chosen universe.
- The commutative ring sheaf is `R : Sheaf J RingCat.{u}` with
  `[∀ U : Cᵒᵖ, IsMulCommutative (R.obj.obj U)]`. The RingCat structure already
  supplies each ring and its restriction maps; the instance says precisely that
  multiplication in every section ring commutes. This uses the general ringed-site
  dependency directly without inventing another module category.
- The category A is the recorded `ringedSiteModules.{u} R`. Its abelian structure
  comes from Mathlib's sheafification on this small site. No enough-projectives
  assumption is imposed.
- The unbounded derived category and chosen morphism universe are
  `DerivedCategory (ringedSiteModules.{u} R)` and
  `[HasDerivedCategory.{w} (ringedSiteModules.{u} R)]`. The localization is
  `DerivedCategory.Q`; shifts and cones are Mathlib's cochain shifts and mapping cones.
- `a b : ℤ` and `hab : a < b` give the stated interval; `P`, `M`, and `K` are
  respectively the module sheaf, derived object, and actual cochain complex.
- `hsupp` says `IsZero (K.X q)` for `q < a ∨ b - 1 < q`, exactly the stipulated
  support [a,b-1]. `hproj : ∀ q : ℤ, Projective (K.X q)` says every term lifts
  along epimorphisms, with no projectivity assumption on P.
- `v₁`, `v₂`, and `δ` are all three maps of the given triangle, whose first object
  is Q of P concentrated in degree b, i.e. P[-b]. `htri` is membership of
  `Triangle.mk v₁ v₂ δ` in `distTriang`, without any extra exactness hypothesis.

Conclusions, clause by clause:

- The existential `g` is an actual map of complexes from K to the single complex
  with P in degree b-1, namely P[-b+1]. `Q.map g` followed by the inverse component
  of `((singleFunctors A).postcomp Q).shiftIso 1 (b-1) b ...` equals `δ`.
  This is the canonical identification of Q(P in degree b-1) with Q(P in degree b)[1],
  not a supplied arbitrary isomorphism or a newly chosen connecting morphism.
- `∀ q, q ≠ b-1 → g.f q = 0` is the component-support clause. The equation
  `K.d (b-2) (b-1) ≫ g.f (b-1) = 0` is the cocycle equation, before postcomposing
  with the canonical `singleObjXSelf` identification with P. Postcomposing gives
  exactly the node's equation in P.
- Existential `D` is constrained by `hD : D = (mappingCone g)⟦(-1 : ℤ)⟧`.
  Thus it is precisely the actual shifted cone, rather than an arbitrary complex
  having the right support. `Nonempty (Q.obj D ≅ M)` is the representation clause.
- `∀ q, q < a ∨ b < q → IsZero (D.X q)` is support [a,b]. `eLow q hq`
  identifies its terms below b with K's, and `eTop` identifies the term at b with P.
  Their homomorphisms are explicitly constrained to be the canonical shifted-cone
  projections. The formula uses `eqToHom hD`, `shiftFunctorObjXIso`, and
  `mappingCone.fst`; at the top it uses `mappingCone.snd` followed by
  `singleObjXSelf`. These equations prevent changing the sign by secretly choosing
  a negative top-term identification.
- The lower differential equation for `q+1 < b` identifies it with `K.d q (q+1)`.
  The transported last differential is explicitly the negative of
  `g.f (b-1) ≫ singleObjXSelf.hom`. Mathlib's cone is the source-shifted term plus
  target term; reordered as the node's (target, source), its differential is
  `(d_T y + g x, -d_K x)`. Shifting by -1 gives the displayed negative last map.
- The final existential `Dplus`, `e : D ≅ Dplus`, `ePlusLow`, and `ePlusTop` states
  the isomorphic attached complex. The component equations make e identity below
  b under the term identifications and minus identity at b. Its lower differentials
  are K's and its last differential is the positive component of g. Its remaining
  terms are zero because it is isomorphic to D.
- The conditional finite-free clause assumes exactly that P and every K.X q are
  isomorphic to `SheafOfModules.free (ULift (Fin n))` for some natural n, and
  concludes the same for every D.X q. `free` is Mathlib's coproduct of unit R, so
  this is a finite direct sum of C as a module sheaf. No new finite-free predicate
  is introduced. The isomorphic attached complex inherits the same property.
- There is no nonzero hypothesis on P, K, or the ranks. There is no restriction on
  the entries of g or an underlying constant-ring presentation.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, the recorded general-site abbreviation of
  `SheafOfModules`, including its docstring and inherited abelian interface.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, the triangulated
  and shift instances, and the single-functor compatibility. This is the recorded
  abstract-derived-category dependency.
- The proof-only import `Mathlib.Algebra.Homology.DerivedCategory.KProjective`
  supplies the proof dependency `CochainComplex.IsKProjective.Qh_map_bijective`;
  its bounded-above projectivity input is
  `CochainComplex.isKProjective_of_projective`.
- The proof-only import `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
  supplies `CategoryTheory.Pretriangulated` and
  `CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂`, the recorded triangulated
  structure and triangle-morphism-isomorphism dependencies.
- The public `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free` supplies the finite
  coproducts of the coefficient unit. `Mathlib.Algebra.Category.Grp.FilteredColimits`
  supplies the concrete sheafification instances used for the abelian category of
  module sheaves on a small site. `HomologicalComplex.singleObjXSelf`, the cone
  projections, and `CochainComplex.shiftFunctorObjXIso` are the existing canonical
  term identifications, read in the corresponding Mathlib Single, MappingCone,
  and Shift sources.

Edge cases checked mathematically before and after writing:

- P=0: the single target and g vanish, so the shifted cone identifies with K.
  The existential projection isomorphisms remain valid; no positive-rank binder occurs.
- K=0: D is P in degree b, matching the triangle; projectivity of zero is allowed.
- b=a+1: the lower-differential clause concerns zero-supported lower terms and
  the only possible nonzero differential is -g^a, or +g^a in Dplus.
- a and b can be negative; the support, degrees, and shifts use integers throughout.
- Rank zero uses the empty `Fin 0` coproduct. The empty site is allowed.
- Taking g=id with a single nonzero source term yields the usual acyclic two-term
  complex, and the canonical projections give its negative last differential.

Searches actually run via `msearch.py Q38 lem-sf-projective-top-cell-attachment`:

- `leanfinder`: “A triangle from a shifted module sheaf to M to a bounded projective
  complex is represented by attaching its top term with the connecting map”. Eight
  results, including `ShortComplex.ShortExact.singleTriangle`,
  `Triangulated.TStructure.triangleLTGE`, `DerivedCategory.triangleOfSES`, and
  `CochainComplex.mappingCone.triangle`; none is the full attachment statement.
- `loogle`: `"CochainComplex.mappingCone"`. Twelve results including mappingCone,
  its fst/snd/inl/inr maps, cochain lifts/descs, and isZero_X_iff. These provide
  canonical ingredients but not the theorem.
- `grep`: `mappingCone.*single|single.*mappingCone|topCell|top_cell`, subdirectory
  `Mathlib/Algebra/Homology`: zero hits.
- `leansearch`: “Bounded projective complex connecting morphism to a single term is
  represented by a chain map whose shifted cone attaches the last term”. Eight
  results, including `HomologicalComplex.mkHomToSingle`, `mkHomFromSingle`,
  projective-resolution maps, and mappingCone triangles. None states all clauses.
- Repository `rg` for `topCell|top_cell|projective.*attachment|` followed by this
  node id in `lean/WeilConjectures` and `lean/Sheaf` returned no matches; a separate
  `grep -rn` of the node id in `lean/WeilConjectures` also returned none.
  Broader `FiniteFree|IsFiniteFree|finiteFree` and definition searches found free
  sheaves, Hom comparisons and finite-free zero models, not this statement.

Validation: `scompile.py` compiled both its private sandbox check and the module
`Sheaf.Paper.ProjectiveTopCellAttachment` cleanly (5.1 s and 4.5 s). The initial
syntax errors in the two dependent isomorphism binders were repaired by parentheses.
No warning remained. Every universe and variable is explicitly bound; the only
small arithmetic proofs inside the signature establish index equalities/inequalities,
and the sole mathematical theorem proof remains `sorry`.

## Second reading by Q38

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
