## Worker report

Item: `lem-trf-smooth-section-centred-coordinates`, group Q82, 2026-10-21 UTC.
Module: `Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates`.
Main declaration:
`AlgebraicGeometry.SmoothSectionCentredCoordinates.exists_centred_coordinates`.
The only postponed proof is this theorem, with the node's ten proof steps in its
docstring. The helper structure `Chart` packages its existential chart witnesses;
it introduces no alternative scheme, regular-sequence, conormal, or symmetric-algebra
notion. No new node, dependency repair, or statement correction was necessary.

### Hypotheses

| Node hypothesis | Lean rendering |
| --- | --- |
| Schemes V and S | `{V S : Scheme.{u}}`, with the universe explicitly declared |
| S Noetherian, meaning a finite affine cover by Noetherian rings | `[IsNoetherian S]`; Mathlib's class extends locally Noetherian and compact, precisely equivalent to the stated finite affine cover |
| Integer d at least zero | `(d : ℕ)` |
| Morphism g : V → S, smooth of pure relative dimension d | `(g : V ⟶ S) [SmoothOfRelativeDimension d g]`; this is the dependency's recorded standard-smooth local dimension condition and entails smoothness |
| g separated | `[IsSeparated g]` |
| g of finite type | `[LocallyOfFiniteType g] [QuasiCompact g]`, the dependency's prescribed conjunction |
| Closed section s | `(s : S ⟶ V) [IsClosedImmersion s]` |
| g composed with s is identity | `(hs : s ≫ g = 𝟙 S)` |

There is no compactifiability, affineness, nonemptiness, flatness of S, field,
reducedness, characteristic, or regularity hypothesis on the input.

### Conclusions and chart fields

The first conjunct is `∃ (A : Type u) (c : A → Chart d g s), ⨆ a, (c a).T.1 = ⊤`.
It permits an empty indexing type. Each `Chart` renders the local clauses as follows.

| Node conclusion | Lean rendering |
| --- | --- |
| Zariski affine base opens S_i | `T : S.affineOpens`; the supremum condition says these opens cover S |
| Affine neighbourhood U_i in V ×_S S_i | `U : V.affineOpens`, `mapsInto : U.1 ≤ g ⁻¹ᵁ T.1`, and `openInBaseChange : IsOpenImmersion (pullback.lift U.1.ι (g.resLE T.1 U.1 mapsInto) ...)`; this is the actual canonical map into the base change, with its actual two projections |
| U_i contains s(S_i) | `sectionInto : T.1 ≤ s ⁻¹ᵁ U.1`; `sectionPreimage : s ⁻¹ᵁ U.1 = T.1` records the exact intersection with the section |
| Separated etale S_i-map to affine d-space | `e : U.1.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) T.1.toScheme`, its `over` equality, `etale : Etale e`, and `separated : IsSeparated e` |
| Map sends section to zero, and inverse image of zero is the section scheme-theoretically | `zeroFiber : IsPullback (s.resLE U.1 T.1 sectionInto) (𝟙 T.1.toScheme) e (AffineSpace.homOfVector (𝟙 T.1.toScheme) (fun _ ↦ 0))`; its commutativity is exactly centring, and its universal property is the scheme-theoretic equality, not just equality of point sets |
| Polynomial coordinates x_1,...,x_d in B_i | `x : Fin d → Γ(V, U.1)` with `coordinates` identifying them with `e.appTop` on the standard `AffineSpace.coord`, using the canonical `U.1.topIso` |
| P_i = R_i[x_1,...,x_d] → B_i induced by the chart | `MvPolynomial.eval₂Hom (g.appLE T.1 U.1 mapsInto).hom x`; here R_i is `Γ(S, T.1)` and B_i is `Γ(V, U.1)`. These rings give the canonical affine spectra of the chosen opens |
| Induced ring map etale and flat | `algebraEtale` and `algebraFlat` for that very evaluation map |
| I_i = J_i B_i is the section ideal | `sectionIdeal : Ideal.map ... (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) Γ(S, T.1)))) = s.ker.ideal U` |
| B_i/I_i = R_i through the section augmentation | `quotient : Γ(V, U.1) ⧸ s.ker.ideal U ≃+* Γ(S, T.1)` and `augmentation`, requiring its value on every quotient representative b to equal `s.appLE U.1 T.1 sectionInto b` |
| Coordinate list regular, including the injective successive multiplication maps | `regular : RingTheory.Sequence.IsRegular Γ(V, U.1) (List.ofFn x)`; the recorded definition extends weak regularity by the nonzero final quotient condition |
| Conormal coordinate classes form the basis [x_j] | `coordinateLift` and `coordinateLift_value` lift each actual x_j into the actual ideal-power sheaf; `conormalBasis` is a basis of `(ConormalGradedAlgebra.piece s 1)` sections and `conormalBasis_value` identifies its jth vector with the quotient representative of that lift |
| Degree-m multiplication sends each basis monomial to the same coordinate monomial modulo I_i^(m+1) | `monomials` quantifies over every finitely supported exponent vector `α : Fin d →₀ ℕ`. It supplies a section a of the actual `power s α.degree`, with image `α.prod (fun j k ↦ x j ^ k)`. The image under `symmetricComparison s` of the corresponding product of `SymmetricAlgebraSheaf.inclusion` images of the basis vectors equals `homogeneousClass s ... α.degree U.1 a` |
| Identifications commute with restriction | All the monomial expressions are values of the one globally defined sheaf morphism `symmetricComparison s`, the sheaf morphism `SymmetricAlgebraSheaf.inclusion`, and the dependency's homogeneous representative maps. Their naturality supplies compatibility on every smaller open and every overlap; the target is the fixed presentation with its canonical affine-chart representative formula. There are no independently chosen chart comparison maps to reconcile |
| s regular immersion of codimension d | `IsRegularClosedImmersionWithCodimension s (fun _ ↦ d)` |
| E = I/I² on S locally free of rank d | `(ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d`; `piece s 1` is the recorded tensor pullback of I, canonically I/I² |
| Canonical Sym(E) → direct sum I^m/I^(m+1) an isomorphism | `IsIso (ConormalGradedAlgebra.symmetricComparison s)` for the exact map of `lem-pur-conormal-graded-algebra`, not an arbitrary isomorphism |

The degree of α is its sum of exponents. Taking a one-coordinate exponent vector
gives the degree-one formula; taking α = 0 gives the unit in degree zero. The
conormal basis makes these precisely the usual symmetric-algebra basis monomials.
The dependency's `Presentation.affineChart` identifies `homogeneousClass` of a
power representative with `DirectSum.of ... m (Submodule.Quotient.mk ...)`, i.e.
the stated class in I_i^m/I_i^(m+1). Thus the formula uses the specified comparison.
The equality `sectionPreimage` identifies its base open with S_i without changing
any scalar action or choosing an unrelated module.

### Dependency declarations read and used

All statement dependencies were read, including their recorded declaration signatures
and docstrings. The following are reused rather than redefined:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; `Mathlib.AlgebraicGeometry.Noetherian`, `IsNoetherian`
  supplies the equivalent scheme condition of the item.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `SmoothOfRelativeDimension`, which implies the recorded `Smooth` notion.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`, `IsSeparated`. Properness is
  not assumed; the node defines separatedness too.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `LocallyOfFiniteType`, and `QuasiCompact` from its companion module.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `IsClosedImmersion`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `Etale`.
- `def-sbc-affine-space`: the node's Mathlib match,
  `Mathlib.AlgebraicGeometry.AffineSpace`, `AffineSpace`; coordinates use
  `AffineSpace.coord` and the zero morphism uses `AffineSpace.homOfVector`.
- `def-sbc-closed-immersion-ideal-sheaf`: `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`,
  `Scheme.Hom.ker`, used as `s.ker.ideal U`.
- `lem-pur-conormal-graded-algebra`: `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra`,
  `ConormalGradedAlgebra.presentation`, `.symmetricComparison`, `.power`,
  `.powerInclusion`, `.piece`, `.representative` and `.homogeneousClass`. Its
  `Presentation` includes the affine graded class formula and natural sheaf maps.
- `def-weil-pbc-regular-sequence`: `Mathlib.RingTheory.Regular.RegularSequence`,
  `RingTheory.Sequence.IsRegular`.
- `def-per-regular-closed-immersion-codimension`:
  `Sheaf.AlgebraicGeometry.RegularClosedImmersionCodimension`,
  `IsRegularClosedImmersionWithCodimension`.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`:
  its documented scheme convention is the ordinary `Limits.pullback` with
  `pullback.fst` and `.snd`. The chart's `openInBaseChange` uses this construction.
  The module-only `moduleBaseChange` declaration is not a scheme constructor and
  is not substituted for this pullback.

Every stated proof dependency's module is imported. In particular the regular-sequence
graded-polynomial theorem, affine conormal frame, symmetric-algebra affine comparison,
symmetric-algebra free-module polynomial comparison, and quasi-coherent isomorphism
criterion remain ordinary proof-only imports. There is no import of the downstream
finite-ring-section-deformation theorem and no dependency cycle.

### Edge cases checked before writing

- Empty S: the indexing type A may be empty, and the supremum of its opens is the
  top open of the empty scheme. The regular immersion condition is vacuous, the
  conormal sheaf has the unique empty-space frame, and the comparison is invertible.
  Since g maps V to S, V is also empty in this case.
- d = 0: `Fin 0` and the coordinate list are empty. Choose nonempty affine base
  charts when S has points; the zero-fibre square makes the chart the section
  component. Its section ideal is zero and its final quotient is the nonzero
  base ring, so the full `IsRegular` convention holds. The only exponent vector
  is zero, the monomial formula is the unit formula, and the positive degree
  pieces vanish. Empty S uses the empty cover instead of an impossible regular
  sequence in the zero ring.
- Nonreduced and disconnected Noetherian base: no reducedness or connectedness
  assumption is introduced. Polynomial-variable multiplication is injective
  over every ring; flatness transports it. Local nonempty charts give nonzero
  final quotients without assuming the whole base is nonempty.
- Multiple components in the initial zero fibre: the Cartesian `zeroFiber`
  condition forces the clopen complement to have been removed. Merely centring
  the map or identifying its point set would not meet this condition.
- Restriction and changes of chosen bases on overlaps: all displayed polynomial
  images use the global canonical comparison, so naturality applies independently
  of whether two local coordinate bases are equal.
- Universes: every scheme has arbitrary universe u; the affine-space coordinate
  type is `ULift.{u} (Fin d)`. Polynomial coordinates are indexed by `Fin d`, which
  does not restrict the coefficient universe. The cover index type is `Type u`,
  sufficient to index a choice of chart at every point of S.

No statement fault or disputed mathematical assertion was found. The item is an
auxiliary construction in the named blueprint proof, whose Local construction was
opened and read; its ten stage-1 steps justify the Zariski refinement and the
additional conormal algebra conclusions.

### Searches

The required msearch calls were made for Q82 and this exact item:

- LeanFinder: `A closed section of a smooth separated scheme morphism admits centred
  etale coordinates and its conormal symmetric algebra is the associated graded algebra`.
  Eight hits, including the standard-smooth local chart and etale polynomial map;
  no hit states the complete centred-section/conormal assertion.
- Loogle: `AlgebraicGeometry.SmoothOfRelativeDimension, AlgebraicGeometry.AffineSpace`.
  Three hits, all smoothness of affine-space projections, not this statement.
- LeanSearch: `A smooth morphism with a closed section has etale coordinates centred
  on the section`. Eight hits, mainly smoothness constructors and standard-smooth
  local charts, plus an unrelated manifold result; no exact match.
- Mathlib grep through msearch: `exists.*[Cc]oord|[Ss]ection.*[Ee]tale`, subdirectory
  `AlgebraicGeometry`. One hit, an elliptic-curve basis lemma, not this assertion.
- Local `rg -n 'centred|centered|smooth.section|lem-trf-smooth-section-centred-coordinates'`
  over both `lean/WeilConjectures` and `lean/Sheaf`. Hits include etale-neighbourhood
  lifting, formal completions, and the downstream finite-ring deformation geometry.
  None states the full affine centred-coordinate cover and its monomial formulas.
  The downstream geometry theorem additionally assumes compactifiability and omits
  the centred affine chart data, so it is not an existing match and is not imported.
- Exact new namespace/declaration search over `lean/Sheaf` and
  `lean/WeilConjectures`: no declaration named `exists_centred_coordinates` or
  namespace `AlgebraicGeometry.SmoothSectionCentredCoordinates` before this delivery.

### Validation

Used only the authorized `scompile.py Q82 lem-trf-smooth-section-centred-coordinates`
wrapper. Initial elaboration exposed the distinction between a module-valued
inclusion and the underlying ring in the monomial power expression. An explicit
`@id` ring type annotation fixes that coercion without a hidden let or an altered
mathematical statement. The final module compiled under both the sandbox name and
the final library name, without warnings or errors (6.7 s and 6.5 s respectively).
All variables and universes are explicit; all lines are at most 100 characters.

## Second reading by Q82

This section records the dispatcher's worker's second pass over the actual node and
module; no additional agent was started, as the brief forbids it. The maintainer's
independent review remains separate from this delivery.

I reread the statement's first paragraph against the theorem binders and `Chart`:
the base is Noetherian, g has exactly the given relative dimension and finite-type
conditions, and s is closed with the given retraction identity. The local cover
conclusion includes affine opens on both sides, the canonical open immersion into
the base change, the actual etale S_i-map, and its Cartesian zero fibre. I added
`openInBaseChange` in this pass to display the literal open in V ×_S S_i explicitly.
The polynomial homomorphism is tied to e by `coordinates`, and both its constant
map and quotient augmentation are the actual maps of g and s. The regular sequence
uses the recorded full convention, not just weak regularity.

I then reread the second paragraph: the conormal is the dependency's fixed piece,
the basis vectors are the classes of the actual coordinate functions, and the
monomial product is evaluated by the dependency's fixed canonical comparison.
The witnesses a have the required product as image in the ambient structure sheaf,
so its `homogeneousClass` is the required class in degree m, rather than a freely
chosen graded element. The final three conjuncts state exactly codimension d,
locally free rank d, and invertibility of that comparison. All restrictions use
the same sheaf morphisms. No change to the node statement, statement dependencies,
proof, or proof dependencies was made.
