## Worker report

The module `Sheaf.CategoryTheory.SignedFibreTriangulated` states the single theorem
`CategoryTheory.exists_signedFibre_triangulated`, with proof `sorry`. No definitions,
additional nodes, dependency repairs, or statement corrections are required.

The existentially quantified complex functor `F` is characterized in every degree
and on every morphism by the displayed coordinate equations. It is not an arbitrary
functor assumed as a hypothesis. The isomorphisms `e I n` identify its degree `n`
with exactly `A(I.X n) × B(I.X (n-1))`, the finite direct sum in abelian groups.
No construction is selected from an unspecified mere existence theorem.

Hypothesis and clause correspondence, in the order of the node:

| Node | Lean |
| --- | --- |
| An abelian category A | `{C : Type u} [Category.{v} C] [Abelian C]` |
| Additive functors A,B to Ab | `(A B : C ⥤ AddCommGrpCat.{w}) [A.Additive] [B.Additive]` |
| A natural transformation r | `(r : A ⟶ B)` |
| Integer cochain complexes | `CochainComplex C ℤ` and `.up ℤ` throughout |
| Cone degrees L^n plus K^(n+1), differential (d_L x + f y, -d_K y) | Mathlib `mappingCone`, read with its `inl`, `inr`, `fst`, `snd` components; the internal biproduct order is handled by these projections |
| Boundary -p | `(mappingCone.triangle f).mor₃`, whose definition uses `-fst` |
| F(I)^n = A(I^n) plus B(I^(n-1)) | `e : ∀ I n, (F.obj I).X n ≅ AddCommGrpCat.of (A.obj (I.X n) × B.obj (I.X (n - 1)))` |
| D(a,b) = (d_A a, r(a) - d_B b) | First conjunct, the equality for `(F.obj I).d n (n+1)`, conjugated by `e`; `XIsoOfEq (Int.add_sub_cancel n 1).symm` only identifies degree n with (n+1)-1 |
| F(f)(a,b) = (A(f)a, B(f)b) | Second conjunct, the degreewise formula for `(F.map f).f n` |
| Induced additive functor on K(A) | Existential `G` with `_addG : G.Additive`, and natural isomorphism `alpha : F ⋙ quotient Ab ≅ quotient C ⋙ G`; naturality gives precisely the induced maps on homotopy classes |
| Homotopy H induces (A(H)a, -B(H)b) | Third conjunct: `∃ h : Homotopy (F.map f) (F.map g)` with the displayed formula for `h.hom n (n-1)`; other components vanish by the definition of `Homotopy` |
| Shift comparison s_I = (a,-b) | `_shiftF : F.CommShift ℤ` and fourth conjunct for `(F.commShiftIso (1 : ℤ)).hom.app I`; `shiftFunctorObjXIso` supplies only the canonical index identifications |
| Chain isomorphism F(Cone f) ≅ Cone(F f) | `Phi : ∀ {I J} (f : I ⟶ J), F.obj (mappingCone f) ≅ mappingCone (F.map f)` |
| Formula Phi(x,y,z,w) = (x,z,y,-w) | Fifth conjunct: its `snd` projection has `e J n` coordinates `(x,z)` and its `fst` projection has `e I (n+1)` coordinates `(y,-w)`; x,y come from A of the source cone projections, z,w from B of them |
| Naturality of Phi for strictly commuting squares | Sixth conjunct, equality between `F.map (mappingCone.map ...) ≫ (Phi f').hom` and `(Phi f).hom ≫ mappingCone.map ...`; the proof term in the last argument is only `F.map` applied to the given equality h |
| Inclusion of F(J) is respected | First equality in seventh conjunct: `F.map (mappingCone.inr f) ≫ (Phi f).hom = mappingCone.inr (F.map f)` |
| s_I F(-p) = -p Phi | Second equality in seventh conjunct, using categorical composition order: `F.map (triangle f).mor₃ ≫ s_I = (Phi f).hom ≫ (triangle (F.map f)).mor₃` |
| Exact on homotopy categories with this shift | `_shiftG : G.CommShift ℤ`, `alpha.hom.CommShift ℤ`, and `G.IsTriangulated`; compatibility of alpha identifies its shift with the explicitly specified complex-level shift |
| Restriction to bounded-below complexes | Last two conjuncts: `I.IsStrictlyGE N → (F.obj I).IsStrictlyGE N`, and preservation of `HomotopyCategory.plus` by G |

The auxiliary existential additivity and commutation structures are conclusions,
not additional hypotheses. Commutation with all integer shifts is the standard
Mathlib encoding of the node's shift comparison. Degreewise isomorphisms allow
the canonical choices of finite biproducts without changing the specified objects
or formulas. All object, morphism and coefficient universes `u v w` are explicit
and independent; there is no smallness or equality-of-universes assumption.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (the node is a Mathlib leaf).
- `def-weil-abstract-derived-category`: its recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` is publicly imported. The
  statement uses its underlying complex, cone, shift and homotopy framework,
  not a second derived-category definition. Its recorded declarations
  `DerivedCategory` and `HasDerivedCategory` were read in full.
- `def-weil-triangulated-category`: the Mathlib matches
  `CategoryTheory.Pretriangulated`, `CategoryTheory.IsTriangulated`, and
  `CategoryTheory.Functor.IsTriangulated`, from
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `.Triangulated`,
  and `.Functor`. These are available through the public derived-category import.
- Proof dependency `lem-trf-additive-homotopy-category-triangulated`: Mathlib
  `HomotopyCategory.instIsTriangulatedIntUp`,
  `HomotopyCategory.Pretriangulated.distinguishedTriangles`, and
  `HomotopyCategory.mappingCone_triangleh_distinguished`, from
  `Mathlib.Algebra.Homology.HomotopyCategory.Triangulated` and `.Pretriangulated`.
  Those modules are already included by the public derived-category import;
  there is no unstated project module to import.
- Additional standard APIs: `Homotopy`, `CochainComplex.shiftFunctorObjXIso`,
  the canonical `mappingCone` projections and triangle maps,
  `CochainComplex.IsStrictlyGE`, and `HomotopyCategory.plus`. The latter is the
  actual bounded-below representative property, which is not invariant under
  arbitrary homotopy-category isomorphisms; preservation by G is stated explicitly.

Source checked: `literature/stacks-project/derived.tex`, labels `definition-cone`
and `lemma-functorial-cone` (Tags 014E and 014F), together with the DAG's eight
explicit signed-totalization proof steps and the triangulation interfaces above.
The source is an agent-written refinement, as the node explicitly records.

Edge cases checked before finalization:

- Zero complex, zero functors, and the zero natural transformation: the coordinate
  formulas respectively give the zero complex or the sum of A(I) and shifted B(I)
  with the stated negative differential. The shift still changes the B sign.
- Identity transformation A = B: the same formulas give the contractible fibre,
  with no invertibility assumption on r required by the general statement.
- Zero/identity chain maps: no nonzero-map restriction occurs. The cone comparison
  still sends its four coordinates to `(x,z,y,-w)`.
- Degrees 0 and negative degrees are retained because indices are integers.
  Index equalities use integer subtraction, never truncated natural subtraction.
- Boundary sign: F(-p) sends `(x,y,z,w)` to `(-y,-w)`; its shift comparison then
  gives `(-y,w)`, which agrees with the target cone boundary after Phi.
- A complex zero below any N is sent to one zero below the same N, since
  n < N implies n-1 < N. This includes the zero complex and arbitrary lower bounds.
- Coefficients and the category may have independent universes; no finite,
  nonempty, enough-injectives, exactness-of-A/B, or derived-localization hypothesis
  has been introduced.

Searches made before writing (the wrapper recorded their raw results in
`searches.jsonl`):

- LeanFinder: `The signed mapping fibre of a natural transformation between additive functors is triangulated on homotopy categories`.
  Eight results, including the triangulation of `G.mapHomotopyCategory` for a
  single additive functor. None is the signed two-functor fibre statement.
- Loogle: `CochainComplex.mappingCocone, CategoryTheory.Functor.IsTriangulated`.
  Zero hits.
- Mathlib grep: `mappingCocone.*[Ff]unctor|signed[Ff]ib|signed_[Ff]ib`.
  Zero hits. The ordinary `mappingCocone` implementation was also read; it is a
  shifted mapping cone of a single complex map and does not state the present
  functor, comparison formulas or exactness theorem.
- LeanSearch: `Mapping fibre of a natural transformation of additive functors is an exact functor on the homotopy category`.
  Eight hits: single-functor homotopy-category triangulation, right-derived
  functor APIs, Grothendieck-category fibres and `NatTrans.mapHomotopyCategory_app`.
  None states this theorem.
- Ripgrep of the upstream project and `lean/Sheaf` for
  `signedFibre|signedFiber|signed_fibre|signed_fiber|lem-amb-signed-fibre-triangulated`,
  and of `dag/lean_names_upstream.json`: no declaration matching this notion or
  node. A broader signed-fibre prose search found a completed-tensor reflector
  comment, which concerns a different coefficient-completion construction.

Validation: the delivered file was compiled through `scompile.py`, separately
in its sandbox and module path, under the standard 60-second limit. Both compiles
were clean, with no warnings or errors. The theorem has the sole postponed proof.
The node copy changes only `lean`; no statement is disputed or corrected.

## Second reading by Q68

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
