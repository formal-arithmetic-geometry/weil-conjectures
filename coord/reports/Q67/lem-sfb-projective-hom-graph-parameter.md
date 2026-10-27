## Worker report

The module `Sheaf.AlgebraicGeometry.ProjectiveHomGraphParameter` states
`AlgebraicGeometry.exists_projective_hom_graph_parameter`, with one postponed theorem
proof and no new definitions. The natural-language statement is unchanged. Its docstring
records all nine proof steps and their prerequisite nodes. The prescribed `scompile.py`
checked both the sandbox view and the module at its intended library path successfully;
there were no errors or non-sorry warnings.

Hypotheses, individually:

- `S : Scheme.{u}`, `[IsLocallyNoetherian S]`, and `[CompactSpace S]` say that S is
  a Noetherian scheme in the node's quasi-compact and locally Noetherian convention.
- `[IsIntegral S]` says integral, including nonempty. `S.functionField` is K, and
  `genericPoint S` is eta; `S.fromSpecStalk (genericPoint S)` is Spec K → S.
  Choosing the generic stalk itself as K is the canonical function-field convention,
  rather than an additional condition on a separately supplied field.
- `f : W ⟶ S` and `g : Q ⟶ S` specify both structure morphisms.
- `[IsHProjective f]`, `[Flat f]`, `[LocallyOfFinitePresentation f]` say W/S is
  H-projective, flat and finitely presented. H-projectivity implies properness and hence
  quasi-compactness and quasi-separatedness, so local finite presentation is exactly
  finite presentation here. `[IsHProjective g]` says precisely Q/S is H-projective.
- `N`, `i : pullback f g ⟶ ℙ(ULift (Fin (N+1)); S)`, `[IsClosedImmersion i]`, and
  `hi` are the chosen finite projective-space closed embedding and its equality over S.
  ULift changes only the coordinate type's universe.

Conclusions, individually:

- `M : Over S` and `e : (relativeMorphismsPresheaf f g).RepresentableBy M` represent
  the exact relative morphism presheaf from the recorded dependency. Its points are
  maps T ×_S W → Q over S, canonically equivalent by the fibre-product universal
  property to T-morphisms W_T → Q_T. `RepresentableBy.homEquiv` gives the bijections;
  its `homEquiv_comp` field gives compatibility with every test-scheme map. In
  particular T and T' may be arbitrary schemes over any S' → S: the same bijections
  identify the pullback representing object and evaluation after arbitrary base change.
- `MP HP : NumericalHilbertPolynomial → Over S` are the components M_P and H_P;
  `μ` are the coproduct injections and `Nonempty (IsColimit (Cofan.mk M μ))` says
  M is their coproduct in schemes over S. These are therefore open and closed components.
- For every P, `IsHProjective (HP P).hom`, `LocallyOfFiniteType (HP P).hom`, and
  `QuasiCompact (HP P).hom` say H_P is H-projective and finite type over S.
  `IsOpenImmersion (j P).left` and the type `j P : MP P ⟶ HP P` give the stated
  open immersion over S, without a separate projectivity claim for M_P or its closure.
- The `HasProjectiveFibreHilbertPolynomial ... ↔ ∃! b, b ≫ μ P = a` clause specifies
  the polynomial index for the chosen embedding, using the kernel ideal of the actual
  `relativeMorphismGraph` of `e.homEquiv a`. It uses the existing eventual fibre Euler
  polynomial predicate, which is the eventual homogeneous-coordinate Hilbert polynomial
  by its recorded source interpretation. It does not use arbitrary component labels.
- `ev = (e.homEquiv (𝟙 M)).left` supplies universal evaluation. In the equivalent
  map-to-Q convention its domain is M ×_S W. Pairing it with the projection to M
  gives W_M → Q_M. The following identity for every T and a explicitly identifies
  evaluation with pullback along a; all its maps are the canonical `Over.pullback` maps.
- `∀ uη : (relativeMorphismsPresheaf f g).obj (op (Over.mk ...))` quantifies over
  every K-morphism W_eta → Q_eta. The classifying map m has `e.homEquiv m = uη`.
- `P`, `mP`, and `mP ≫ μ P = m` place that classifying point in one component.
- `I = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range m.left))` fixes
  the actual reduced induced closure. There is no arbitrary substitute for R:
  throughout the conclusion R is exactly `I.subscheme`, with inclusion `I.subschemeι`.
  This uses the construction certified by the recorded reduced-induced-subscheme lemma.
- `hR : IsIntegral I.subscheme` gives integrality. The closed map `c` with
  `c ≫ (μ P).left = I.subschemeι` makes this same R a closed subscheme of M_P.
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and
  `LocallyOfFinitePresentation` for `I.subschemeι ≫ M.hom` are respectively
  separatedness, both parts of finite type, and local finite presentation over S.
- `a` is the generic point's factorization over S, and
  `a.left ≫ I.subschemeι = m.left` is compatibility with m. The `IsPullback` square
  whose upper horizontal map is a and whose left vertical map is `𝟙 (Spec K)` says
  exactly that Spec K with this map is the generic fibre of R/S. It thus specifies
  the canonical identification R_eta = Spec K, with its inverse section a.
- `eK : I.subscheme.functionField ≅ S.functionField` identifies k(R) with K.
  The equation `Spec.map eK.hom ≫ ...fromSpecStalk ... = a.left` normalizes this
  field identification by the same generic map, rather than an unrelated field isomorphism.
- The final equality first restricts ev along `I.subschemeι`, then pulls it back along
  a, and obtains `uη.left`. Both maps are the canonical `Over.pullback f` maps.
  By the preceding pullback square this is precisely extension on R's generic fibre.
- No nodal-fibre, normality, no-rational-maps, characteristic, separated-base or
  flat-target hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms;
  `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`; together with
  `CompactSpace` this is the Noetherian convention.
- `WeilConjectures.AlgebraicGeometry.FunctionField` imports the canonical
  `Scheme.functionField` from `Mathlib.AlgebraicGeometry.FunctionField`, the dependency's
  arbitrary integral-scheme clause; its component-product definition is not copied.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`;
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`/`IsSeparated`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType` and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, with scheme
  pullbacks and their canonical maps from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, certifying
  `Scheme.IdealSheafData.vanishingIdeal` and its subscheme as the required reduced closure.
- `Sheaf.AlgebraicGeometry.RelativeMorphismsPresheaf`: `relativeMorphismsPresheaf`
  and `relativeMorphismGraph` exactly as recorded.
- `Sheaf.AlgebraicGeometry.ProjectiveFibreHilbertPolynomial`:
  `NumericalHilbertPolynomial` and `HasProjectiveFibreHilbertPolynomial`. Its existing
  node `def-sfb-projective-fibre-hilbert-polynomial` is added to stmt_deps, as authorized
  for already landed notions; no node or notion is duplicated.
- The already recorded non-Mathlib proof prerequisites are imported without `public`:
  `graphs_open_in_hilbert`, `exists_projective_hilbert_polynomial_representation`, and
  `hProjective_properness`. The reduced-closure and other Mathlib proof prerequisites
  are also available from the stated imports. None of the imports is a downstream
  theorem about the present parameter scheme.

Edge cases checked before writing: the empty source has one morphism to every target
and zero graph polynomial; the empty target with a nonempty source has empty Hom scheme,
so the generic-morphism clause is vacuous. Unrealizable numerical polynomials can have
empty components; the zero polynomial and empty test schemes are retained. A generic
morphism itself forces its parameter point and closure to be nonempty. S integral already
excludes the empty base. N=0 is permitted. No field characteristic is restricted. Test
schemes, base changes and Spec of the function field use the same scheme universe u,
with no smaller independent test universe. Properness of W explains finite presentation;
there is no hidden finite-presentation strengthening. R/S is not asserted proper.

Searches for existing statements (all performed by the prescribed msearch.py wrapper):

- LeanFinder: “The relative Hom functor between projective schemes with flat finitely
  presented source is represented by open Hilbert polynomial components and the closure
  of a function field point has generic fibre Spec of that field”. Eight hits, involving
  Proj properness, toSpecZero, fromSpec and chart constructions; no Hom parameter theorem.
- Loogle: `"Hilbert", "AlgebraicGeometry"`. Zero hits.
- Mathlib grep: `HilbertScheme|[Hh]om[Ss]cheme|[Pp]rojective.*[Hh]om|[Gg]raph.*[Pp]arameter`
  in AlgebraicGeometry. Twelve hits in projective-spectrum and elliptic-curve source;
  no statement representing this Hom functor.
- LeanSearch: “The relative Hom functor of projective schemes is represented by open
  Hilbert polynomial components and the generic point closure has the same function field”.
  Eight hits: abstract local representability, germs, rational-map generic restrictions
  and Proj charts; none is the present theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `projective_hom`, `hom_graph_parameter`, `HomScheme`, and `relativeMorphismsPresheaf`;
  also searched the exact item id upstream. Found the existing presheaf, graph-open and
  Hilbert-component dependencies. `HighGenusHomClosure` is strictly specialized by nodal,
  normality and no-rational-map hypotheses and proves proper closure; it is not this node.
  Its generic arbitrary-index `RelativeHomSchemeData` is not a polynomial component theorem.
  There is no existing exact statement or collision with the chosen declaration name.

The local source of Stacks quot.tex, lemmas Mor-into-Hilb and Mor-into-Hilb-open, was read,
as were the current blueprint unit and all recorded statement-dependency signatures and
docstrings. No statement correction, dependency repair, new node or disputed statement.

## Second reading by Q67

No independent worker reading: the dispatcher brief prohibits starting other agents and
requires direct delivery for the maintainer's independent review. The author reread the
node against the final Lean signature. The explicit graph-polynomial factorization clause
was retained to prevent arbitrary relabeling of coproduct pieces; the actual vanishing
ideal equality prevents substitution of an unrelated model; the `Spec.map eK.hom`
equality fixes the function-field isomorphism by the same generic factorization. The
node's unchanged hypotheses and every conclusion are mapped above. No mismatch remained
on this author check; it is not claimed as an independent review.
