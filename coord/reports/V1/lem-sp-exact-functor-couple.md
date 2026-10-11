## Worker report

The module `lean/Sheaf/CategoryTheory/ExactFunctorCouple.lean` states
`CategoryTheory.BigradedExactCouple.exactFunctor_couple`, with one `sorry` and no new
notions. All object and morphism universes are explicitly bound; `autoImplicit` is false.
No statement correction or dependency replacement was needed. The only edited field of
this item's node copy is `lean`.

### Hypotheses and page indexing

The two categories are arbitrary `C : Type u₁` and `B : Type u₂`, with independent
`Category.{v₁}` / `Category.{v₂}` and `Abelian` instances. The functor is `Φ : C ⥤ B`.
`[Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]` is exact additivity
between abelian categories, with no faithfulness or preservation of infinite limits
assumed. The couple is the recorded `X : BigradedExactCouple C 0`.

The dependency indexes `pageCouple r` by the number of derived steps, so its actual page
is `R = r + 2`. Throughout the signature `r : ℕ` covers all actual pages `R ≥ 2`.
The node's `(u,v) = (p-R+2,q+R-2)` is therefore `(p-r,q+r)` in Lean. In particular,
`r = 0` is the initial couple, not an extra page before page two.

### Clause 1: the mapped datum is an exact couple

`∃ Y : BigradedExactCouple B 0` asserts all three exactness conditions and zero
composites by the dependency's structure. `hD` and `hE` identify its components with
`Φ.obj (X.D p q)` and `Φ.obj (X.E p q)`. The first three universal equations identify
its `alpha`, `f`, and `g` with their images under `Φ`, transporting endpoints by those
object equalities. Thus `Y` is precisely the image datum, not an unspecified exact
couple merely isomorphic to some image.

### Clause 2: every derived couple and its differential

`δ r p q` and `φ r p q` are the D and E comparisons from the image of the r-th
iterated couple to the r-th iterated image couple. Their initial values are
`eqToIso (hD p q)` and `eqToIso (hE p q)`, i.e. identities after the initial component
identifications. The families `iX` and `iY` are the inclusions in the original D
components: their index-zero values are identities, and each successor is the previous
inclusion composed with the recorded `derivedDInclusion`. Both are mono. The equation
`(δ r p q).hom ≫ iY r p q = Φ.map (iX r p q) ≫ eqToHom (hD p q)` says precisely
that the two subobjects of the initial mapped D agree. This is how equality of D terms
*as subobjects* is rendered without demanding equality of chosen image objects.

The next three equations give the commutative alpha, f, and g squares, including the
shift `(p+r,q-r)` for g. Together with invertibility of δ and φ they assert the
isomorphism of exact couples. The next equation is the differential square, with target
`(p+2+r,q-1-r)`, i.e. `(p+R,q+1-R)`.

The successor comparison is characterized by a map `k` on cycles. Its inclusion equation
makes it the unique kernel map induced by `φ r`; `IsIso k` states that this is the kernel
comparison isomorphism. The equation involving `Φ.map derivedEProjection` and
`φ (r+1)` makes the latter the uniquely induced map on the quotient of cycles by
boundaries. These two equations say exactly that `φ (r+1)` is the cohomology map
induced by `φ r`, composed with the exact-functor homology comparison; they do not allow
an arbitrary isomorphism between the next pages. This universal characterization avoids
introducing a second definition of the cohomology comparison.

### Clause 3: half-plane hypotheses, abutment, filtration and limiting comparisons

The conditional part quantifies `a : ℤ` and the two original vanishing assumptions:
`q < a → IsZero (X.D p q)` and `(p < 0 ∨ q < a) → IsZero (X.E p q)`.
Its first two conclusions are the identical assumptions for Y and the same a.

`LX`, `LY` use the dependency's `LimitSubobjects`; `AX`, `AY` use its `AlphaColimit`.
`hAX`, `hAY` identify the abutment objects with `X.D 0 n`, `Y.D 0 n`.
The equations at the colimit inclusion `ι 0` fix those identifications to the identity.
`eA n`, together with the equation for every `ι p`, identifies the abutment of Y with
the image of the abutment of X, using the same mapped D components. This uses the
canonical colimit maps and does not assume Φ preserves arbitrary colimits.

The existing `imageFiltration` defines each step as the image of `ι p`. For nonnegative
p, the cocone equations and identity at zero say this is the image of the p-fold alpha
map specified in the node. For `p ≤ 0` the signature explicitly says both steps are top.
Both filtrations are finite, and `ConvergesTo` asserts their convergence, hence their
exhaustiveness and separatedness as in the half-plane theorem. `τ n p` commutes with
the step inclusions and `eA n`, stating equality of the transported filtration
subobjects. `κ n p` compares the recorded `gradedPiece` objects. Its cokernel projection
square characterizes the comparison induced by exactness on the successive quotients.

The stabilization condition is `(r : ℤ) + 2 > max (q-a+1) p`, precisely the node's
actual-page bound. `sX` and `sY` satisfy the dependency theorem's kernel-inclusion / page
projection equations, so they are the canonical cohomology stabilization maps.
`Φ.map sX.hom ≫ φ (r+1) = φ r ≫ sY.hom` is their compatibility square.

`φInfinity` is the infinite-page comparison. The `toPageInfinity` equation fixes its
canonical value on the original D maps. For every stabilized page, `hZX` / `hZY`
identify its cycles with the limiting cycles; `eX` / `eY` identify its page with
`pageInfinity` by an equation on the cycle quotient projection. Their square with
`φ r` and `φInfinity` says the latter really is induced by the former under the
canonical stable-page identifications. The `ξX` / `ξY` equations use the existing
`toGradedPiece` and `toPageInfinity` maps to characterize the infinite-page / graded-piece
identifications. Their square with `κ` states the same limiting compatibility.

The last universal clause uses `(r : ℤ)+2 ≥ max (p+3) (q-a+2)`, precisely the stronger
bound in the node. `lambdaX` and `lambdaY` identify each abutment with its D component
at `(p-r,q+r)`. Their inverses are prescribed to be the canonical colimit maps `ι (p-r)`;
because `ι 0` is the identity, the cocone identities characterize these as the node's
iterated alpha maps from index zero to the negative first index. The isomorphisms `tX`
and `tY` identify the p-th filtration step with the corresponding iterated D term; their
inclusion equations say that this is exactly its image under lambda. `ψX` and `ψY`
are characterized by the equation `quotientProjection ≫ ψ = t ≫ g_r`, with only
arithmetic endpoint casts. Thus they are exactly the isomorphisms induced by g_r
through the two filtration steps, rather than unspecified graded-piece isomorphisms.
The kernel of this epimorphic g_r is the image of incoming alpha by the exact-couple
structure, which is the transported next filtration step. The final square is
`Φ.map ψX.hom ≫ (φ r p q).hom = (κ (p+q) p).hom ≫ ψY.hom`, the node's final equation
written in Lean's left-to-right composition convention.

### Dependencies and sources read

- `def-sp-abelian`: `CategoryTheory.Abelian`, `Mathlib.CategoryTheory.Abelian.Basic`.
  Read the full class and docstring: finite products, kernels, cokernels, normal
  monos and epis; zero objects and biproducts follow as documented.
- `def-sp-exact-couple`: `Sheaf.CategoryTheory.ExactCouple`,
  `CategoryTheory.BigradedExactCouple`, `derived`, `pageCouple`, `d`,
  `derivedDInclusion`, `derivedEProjection`. Read the whole module, including
  `DerivedMaps` and its canonical restriction equations.
- `thm-sp-half-plane-convergence`: `Sheaf.CategoryTheory.HalfPlaneConvergence`,
  `CategoryTheory.BigradedExactCouple.halfPlaneConvergence`. Read its full signature
  and proof docstring; its stabilization equation is used verbatim.
- `def-sp-filtration`: `Sheaf.CategoryTheory.Filtration`,
  `CategoryTheory.DecreasingFiltration`, `step`, `gradedPiece`, `IsFinite`.
  Read the whole module. No new filtration or quotient definition is introduced.
- `def-sp-convergence`: `Sheaf.CategoryTheory.ExactCoupleConvergence`,
  `CategoryTheory.BigradedExactCouple.LimitSubobjects`, `AlphaColimit`,
  `cycleBoundaryTower`, `pageInfinity`, `toPageInfinity`, `imageFiltration`,
  `toGradedPiece`, `ConvergesTo`. Read their signatures and docstrings in the module.

The single import is the recorded half-plane-convergence module, which imports the other
three project dependencies and Mathlib's abelian category definitions transitively.
Also read the full node proof and `DerivedCoupleExact.lean` for the iterated inclusion
conventions. The repository's literature checkout is absent on this machine. Opened
Stacks [011Q](https://stacks.math.columbia.edu/tag/011Q),
[011R](https://stacks.math.columbia.edu/tag/011R) and
[011S](https://stacks.math.columbia.edu/tag/011S) directly to check the exact-couple,
derived-couple and page conventions. The functor-transport assertion is the node's
own argument, as its source record explicitly says; it is not claimed as a Stacks theorem.

### Edge cases

Checked zero objects and the zero functor: all comparisons become comparisons of zero
objects, and the equations remain meaningful. No faithful/conservative-functor hypothesis
was inserted. Negative p and q, arbitrary integer a, and total degree below a are
included. At p = 0 the filtration is the whole object and the colimit comparison is the
initial D comparison. For p < 0, the filtration steps are both top and the graded pieces
vanish; the prescribed stabilized g quotient is still well typed. There is no assumption
that the abelian categories have infinite limits or colimits; these are supplied in the
half-plane conclusion by `LimitSubobjects` and `AlphaColimit` universal properties.
The initial actual page two is covered by r = 0, with identity comparisons. The strict
stabilization bound and the stronger non-strict final bound use actual page numbers
r+2; neither has been rounded or replaced by a weaker bound. No characteristic or
coefficient restrictions arise.

### Searches and validation

Ran the prescribed search script for this item; queries/results are logged in
`searches.jsonl`:

- LeanFinder: `An exact additive functor transports exact couples, their derived couples,
  spectral sequence pages and abutment filtrations`: eight hits, including
  `Functor.exact_tfae`, `ShortComplex.ShortExact.map_of_exact`, `ShortComplex.Exact.map`
  and `Functor.preservesHomology_of_map_exact`; these are ingredients, not the theorem.
- Loogle: `Functor.PreservesHomology, Subobject.map`: zero hits, unknown identifier
  `Functor.PreservesHomology` reported by the service.
- Mathlib grep: `ExactCouple|exactCouple|exact couple|def map` in
  `Algebra/Homology/SpectralSequence`: zero hits.
- LeanSearch: `exact functor preserves exact couples spectral sequences`: service
  unavailable (Internal Server Error); no mathematical verdict inferred from that failure.
- Source grep/rg: `lem-sp-exact-functor-couple|ExactCouple|exact couple` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: no hits.
- Project rg for `exact.couple|ExactCouple|halfPlane|HalfPlane` in `lean/Sheaf`: the
  dependency modules, truncation-couple material and Leray/page-induction statements,
  but no exact-functor transport statement.
- Name-collision rg for `exactFunctor_couple` over `dag/lean_names_upstream.json`,
  `lean/Sheaf`, upstream WeilConjectures and Mathlib: no hits.

The final module compiled on the server in 2.5 seconds, exit code 0, with no warnings.
The theorem proof remains `sorry`, as required for stage 2. The independent second
reading is intentionally left to the second reader.

## Second reading by V1

I reread the node statement, its Stacks source (Homology §12.21, Tags 011Q,
011R, 011S, and 0AMJ), all dependency declarations, and the module signature.
The objects and clauses render as follows.

- The arbitrary abelian categories are `C : Type u₁` and `B : Type u₂`, with
  independent category universes and `[Abelian]`; `Φ : C ⥤ B` has
  `[Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]`; and
  `X : BigradedExactCouple C 0` is the input. These are exactly the node's
  hypotheses, with no faithfulness, finiteness, characteristic, or universe
  restriction added.
- The first conclusion introduces `Y : BigradedExactCouple B 0`, object equalities
  `hD` and `hE`, and the three equations for `alpha`, `f`, and `g` under `Φ`.
  Together with the structure's exactness fields this is precisely the mapped exact
  couple of clause 1.
- The next block introduces `δ`, `φ`, and the inclusions `iX`, `iY`; fixes their
  page-zero values, successor recurrences, monicity, and the subobject comparison;
  then gives the alpha/f/g/differential squares and the kernel and quotient
  characterizations of `φ (r+1)`. This is clause 2, including the page shift
  represented by `pageCouple r` (actual page `r+2`).
- The final block universally quantifies the same integer `a` and the two vanishing
  hypotheses, transfers them to `Y`, introduces `LimitSubobjects`, `AlphaColimit`,
  abutment identifications, image filtrations, convergence, graded-piece
  comparisons, stabilization comparisons, the infinite-page comparison, and the
  final stabilized filtration-to-page isomorphisms and square. The inequalities
  `(r : ℤ) + 2 > max (q-a+1) p` and `≥ max (p+3) (q-a+2)` are the node's bounds.

Edge cases were checked: `r = 0` is the initial actual page 2; zero and empty
objects/categories are allowed by the abelian assumptions; negative `p` and `q`,
all integer `a`, and total degree below `a` remain quantified; `p ≤ 0` filtration
steps are explicitly top; no characteristic or infinite-(co)limit assumptions are
introduced. The independent universes cover all cases in the node.

I searched Mathlib, the slopmaster2 source, and project `lean/Sheaf` (including
LeanFinder/Loogle and repository grep); only component lemmas such as preservation
of homology were found, and no existing exact-couple transport statement exists.
The dependency declarations `BigradedExactCouple`, `LimitSubobjects`,
`AlphaColimit`, `imageFiltration`, `ConvergesTo`, and the filtration notions were
opened and match their cited nodes. No mismatch was found, so no source or node
change was necessary. The module compiles with only its intentional theorem `sorry`.
