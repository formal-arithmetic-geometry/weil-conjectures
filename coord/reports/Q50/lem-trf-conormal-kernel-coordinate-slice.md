## Worker report

Stage 2, Q50: states `AlgebraicGeometry.exists_conormalKernelCoordinateSlice` in
`Sheaf.AlgebraicGeometry.ConormalKernelCoordinateSlice`. The theorem's proof is `sorry`.
The module also gives the concrete canonical map `conormalCoordinateFibreMap` and a
`ConormalKernelCoordinateSlice` structure bundling this theorem's existential witnesses.
The structure does not choose any witnesses or derive data from a postponed theorem.
Only the item's `lean` record changes; its accepted statement and split are preserved.

The inherited BLOCKED ending concerned reopening the stage-1 split. The current item
is in stage 2 in `coord/queue.tsv`, has no Lean record, and has an accepted Q137
stage-1 review dated 2026-10-23. The explicit stage-handoff rule in brief-stage2 section 0
therefore directs this statement delivery through deliver2.py. There is no repair note
for this item and no item-specific Q50 return to repair.

### Hypotheses and objects

- The field `k` is `(k : Type u) [Field k]`.
- The ambient algebra `B` is `(B : Type u) [CommRing B] [Algebra k B]` with
  `[Algebra.Smooth k B] [Algebra.FiniteType k B]`, exactly the smooth finite-type
  algebra in the statement. The algebra smoothness is the dependency's recorded notion.
- The ideal and prime are `(I p : Ideal B) [p.IsPrime]`; `(hp : I ≤ p)` is precisely
  the containment hypothesis. There is no maximality or rationality hypothesis on p.
- `A` is literally `B ⧸ I`; `M` and `X` are the spectra of `B` and `B ⧸ I`.
  The closed immersion is the spectrum of the quotient homomorphism.
- `L` is represented by `p.ResidueField`, the prime-local-ring residue field. This
  is canonically kappa(p/I): both fields are the fraction field of B/p. This uses
  the existing prime-residue-field interface, not a new arbitrary coefficient field.
- `V` is `p.ResidueField ⊗[B] KaehlerDifferential k B`. The order of tensor factors
  uses the dependency's recorded commutativity identification.
- `K` is literally `LinearMap.ker (conormalCoordinateFibreMap k B (B ⧸ I)
  p.ResidueField)`. That map is `LinearMap.baseChange` of
  `KaehlerDifferential.map k k B (B ⧸ I)`. On differential generators it sends
  l tensor db to l tensor d(b mod I), so it is the canonical map, not an arbitrary
  linear map with a prescribed kernel. Its surjectivity is the quotient conormal
  sequence. Writing its target as L tensor_B Omega(A/k) is canonically the same
  as L tensor_A Omega(A/k), since the B-actions on both factors factor through A.
- `n_eq` and `r_eq` identify `n` and `r` with the stated `Module.finrank`s.
  The basis fields also witness finite dimensionality and enforce r <= n.

### Each conclusion

- `C` and its algebra structures give the coordinate ring of the affine open W.
  `openImmersion` says Spec C -> Spec B is the morphism induced by the actual
  B-algebra structure and is an open immersion. `point` and `point_eq` assert
  that this open contains p. The usual Gamma-Spec isomorphism identifies C with
  Gamma(W,O_W); W is not an unrelated affine scheme or an arbitrary etale cover.
- `f : Fin r → C` and `f_mem` are the r functions in the ideal of X intersect W,
  namely `I.map (algebraMap B C)`.
- `g : Fin (n - r) → C` gives exactly the remaining n-r functions.
- `fibreIso` and `fibreIso_map` identify V with the differential fibre on W by
  the canonical map induced by B -> C. This records the restriction identification
  used to interpret df_i and dg_j as elements of V.
- `kernelBasis` is a basis of the actual kernel K, indexed by Fin r;
  `kernelBasis_eq` identifies its vectors with the differentials of the chosen f_i
  after that canonical restriction. It does not merely specify an abstract basis.
- `ambientBasis` is a basis of V indexed by `Fin r ⊕ Fin (n-r)`.
  `ambientBasis_f` and `ambientBasis_g` identify its first and second blocks with
  the df_i and dg_j. This disjoint union is the ordered first-r/remaining-n-r
  coordinate set, canonically equivalent to Fin n because the basis forces r <= n.
- `etale` is etaleness of the spectrum of `MvPolynomial.aeval (Sum.elim f g)`.
  Thus the actual prescribed coordinate map e is etale. Polynomial spectra are
  the existing affine-space model identified by `AffineSpace.SpecIso`.
- M_0 is literally Spec(C / span(range f)). The quotient map gives its closed
  immersion in W. No additional choice of a subscheme or its equations occurs.
- `contains` is `Ideal.span (Set.range f) ≤ I.map (algebraMap B C)`.
  This expresses the containment X intersect W inside M_0 scheme theoretically,
  including its nilpotents; containment of underlying sets is not substituted.
- `cartesian` is an `IsPullback` with top map the quotient closed immersion,
  left map the spectrum of the evaluation g_j modulo (f), right map e, and
  bottom map the spectrum of polynomial evaluation sending the first r coordinates
  to zero and the remaining coordinates to their corresponding variables.
  It therefore states precisely the coordinate-subspace base change and fixes
  the remaining-coordinate map, rather than asserting an unspecified pullback.
- `smooth` states smoothness of the whole Spec(C/(f)) over Spec k, not just
  smoothness at the selected point.
- `quotientIso` identifies V/K with the differential fibre of C/(f).
  `kernelBasis` identifies K with the span of the df_i, giving the exact quotient
  in the node. `quotientIso_map` requires the quotient map to be the canonical
  differential-fibre map induced by B -> C/(f). It rules out an arbitrary
  dimension-counting isomorphism.
- Tensor products for W and M_0 are taken over B after restriction of scalars.
  Since Spec C is an open neighbourhood of p, L tensor_B C = L canonically;
  the image of I, and hence (f), is killed in L. These expressions are exactly
  the usual residue fibres over C and C/(f), respectively. They do not assume
  a new or arbitrary extension of L.
- There is no smoothness or reducedness hypothesis on A or X. For r=0,
  `Set.range f` is empty and its span is the zero ideal; the slice is canonically
  Spec C = W, using the standard quotient-by-zero identification. The coordinate
  subspace then is the whole affine space, as required.

### Dependency declarations

Read the recorded signatures and docstrings in their source modules. All are reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
  For the affine hypothesis the finite-type algebra is `Algebra.FiniteType k B`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  the slice and X use the existing quotient-spectrum construction.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, its restriction isomorphism and
  `relativeDifferentialsSpecIso`. These justify the algebraic affine-fibre rendering.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`,
  `KaehlerDifferential.D`, `linearMapEquivDerivation` and `KaehlerDifferential.map`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`: `Ideal.ResidueField` and the
  prime-residue-field algebra interface used to express its affine model.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct` and
  `LinearMap.baseChange`, with the recorded left-factor convention.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace` and `AffineSpace.SpecIso`.
  The coordinate maps are spectra of the actual polynomial evaluation maps.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its base-change
  conventions. The displayed square uses the existing `CategoryTheory.IsPullback`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`.
- `Mathlib.RingTheory.Smooth.Basic`: `Algebra.Smooth`.

Proof-only imports also retain the accepted proof plan: tensor right exactness,
affine-open bases, tilde stalk localization, tensor quotients and affine pullbacks,
the prescribed-coordinate criterion in `Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials`,
etale implies smooth in `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`,
and affine-space smoothness in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
The theorem's docstring describes all eight accepted proof steps and names their inputs.

### Sources and edge cases

Read Stacks `algebra.tex`, lemma-differential-seq (00RU), and `morphisms.tex`,
lemma-etale-at-point (02GU), lemma-smooth-omega-finite-locally-free (02G1), and
lemma-base-change-etale (02GO). This is the DAG's stated coordinate-slice consequence,
not a claim that a single Stacks tag states the entire assertion. The current blueprint
ancestor is in the trace-formula curve-zero unit; its reviewed historical branch is
preserved and no unit statement or proof route is changed.

Checked I=0 (K=0, no equations), r=0 (zero ideal, slice W), r=n (no g-coordinates,
zero-dimensional smooth slice), n=0 (both coordinate sets empty), and arbitrary
nonclosed primes. The zero ring B has no prime p and hence supplies no instance of
the hypotheses; I=B likewise cannot satisfy hp. With B=k[t], I=(t^2), p=(t), K=0
in every characteristic: d(t^2) has zero residue class. The theorem then permits
W itself as slice, so it does not accidentally impose reducedness on X. With
I=(t), p=(t), r=n=1 and the slice is zero dimensional. No perfectness assumption
on k or separability assumption on kappa(p)/k was introduced.

### Searches and validation

The inherited sandbox `searches.jsonl` records the actual msearch calls:

- LeanFinder: “Choose functions whose differentials form the conormal kernel and
  complete to etale coordinates on a smooth algebra with a smooth zero slice”.
  Eight hits, including `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
  and standard-etale presentations. These are general chart/presentation interfaces,
  not the simultaneous conormal-kernel basis and canonical zero-slice quotient here.
- Loogle: `KaehlerDifferential, Algebra.Smooth`: no hits.
- Mathlib grep: `conormal.*slice|etale.*basis|mapBaseChange`, RingTheory:
  hits in Smooth.Basic and Etale.Kaehler; they supply general differential and
  smooth/etale tools, not this statement. The concrete map here is a composition
  of their existing constructions, not a replacement differential notion.
- LeanSearch: “An arbitrary closed subscheme of a smooth affine scheme has a smooth
  local envelope cut out by equations whose differentials form the kernel of the
  cotangent fibre map”. Eight hits including formal-smoothness criteria and the
  general ideal-sheaf subscheme construction; no exact coordinate-slice statement.
- Project rg: the exact node id, `ConormalKernelCoordinate`,
  `conormalKernelCoordinate`, `conormal.*slice|etale.*basis|mapBaseChange`, and
  conormal/coordinate-slice keywords in WeilConjectures and Sheaf. No exact existing
  declaration. General conormal sheaves and regular-immersion results do not give
  this conclusion for an arbitrary, possibly nonreduced, X. In particular a
  conormal injection or a smooth-closed-subscheme hypothesis would change the node.

The canonical fibre-map helper is built in full from `LinearMap.baseChange` and
`KaehlerDifferential.map`. Its only role is to name the map appearing repeatedly
in this node. The witness structure only packages the clauses above. No new
independent mathematical notion or dependency repair is needed.

Server scompile.py checks of the module succeeded with no errors or non-sorry warnings.
The delivery dry run and final push are run after completing this report.

## New nodes

None.

## Dependency modules

None.

## Second reading by Q50

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
