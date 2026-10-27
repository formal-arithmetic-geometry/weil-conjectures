## Worker report

The module `Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus` states
`AlgebraicGeometry.HilbertCoefficient.implicitTaylorCoordinateCalculus`. Its only
postponed proof is that theorem's `sorry`. It includes the complete fifteen-step
natural-language proof from this node. All definitions have real data. The three
conclusion structures contain specifications, not chosen existence witnesses.

The node's statement, proof and proof dependencies remain unchanged. Its statement
dependencies gain two already-landed definitions: `def-trf-regular-hilbert-coefficient-datum`
for its existing `isTaylorMap` interface, and `def-sbc-closed-immersion-ideal-sheaf`
for quasi-coherent ideal-sheaf data. These do not depend on the item. No new DAG
node and no dependency repair is needed.

The main theorem takes an arbitrary scheme B, not an affine replacement. A ring
homomorphism c from k[W,Y] to its global sections specifies the coordinate
morphism by the usual global-section/Spec adjunction. Its restriction along C
specifies the structure morphism. This is exactly a chart over k; no separate
or unrelated algebra structure is introduced. Polynomial spectra represent
A_k^(m+r) and A_k^m, using the affine-space identification in the existing
`def-sbc-affine-space` dependency. The source's finite numbers of variables are
`Fin m`, `Fin r` and `Fin t`; all three may be empty.

The outer existential constructs the regular coordinate derivations before
quantifying the equations h and the center a. This allows the actual Jacobian
hypothesis to be stated, without assuming derivative data as an extra input.
The normalization, scalar and restriction fields characterize the usual
coordinate derivations and force their local uniqueness. A Z-derivation
annihilating the specified image of k is exactly the unbundled k-derivation.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| k is a field of characteristic zero | `{k : Type u} [Field k] [CharZero k]` |
| B is the smooth finite-type k-scheme | `B : Scheme.{u}`, `hs : Smooth (implicitStructureMorphism c)`, and `hft : LocallyOfFiniteType ... ∧ QuasiCompact ...` |
| The given (w,y) coordinates define an etale chart | `c` and `hc : Etale (implicitCoordinateMorphism c)`; `implicitCoordinatesOnOpen` and `implicitCoordinatesAt` are actual restrictions and germs of c |
| Regular functions h_1,...,h_r and a point a | `h : Fin r → Γ(B, ⊤)` and `a : B`, inside the conclusion after the coordinate derivations are constructed |
| h vanishes at a | `∀ i, B.Γevaluation a (h i) = 0` |
| The y-Jacobian is invertible at a | `B.Γevaluation a (implicitJacobian D h) ≠ 0`; evaluation is in the residue field, so this is precisely invertibility there |
| Restriction to the full nonvanishing locus, containing a | `implicitJacobianOpen D h = B.basicOpen (implicitJacobian D h)` and `ImplicitTaylorCalculus.center_in_open` |
| N = V(h), with its scheme structure | `implicitEquationIdeal` is the span of the restricted h, `implicitZeroScheme` is its actual closed subscheme, and `implicitZeroInclusion` is its canonical map to B |
| N is smooth and the original w restricts to etale coordinates | `ImplicitTaylorCalculus.smooth`, `.etale`, and the actual ring map `implicitTangentialCoordinates`, obtained by restricting c along the inclusion and polynomial rename |
| Every b in N, without a closed-point restriction | `.points : ∀ b : implicitZeroScheme D h, Nonempty (ImplicitTaylorPoint ... b)` |
| L = kappa(b) and the actual local rings | Every point field is exactly `N.residueField b`; the domains are `B.presheaf.stalk (j b)` and `N.presheaf.stalk b`. Their residue comparison is the canonical `j.stalkMap b ≫ N.residue b` |
| Centered local Taylor maps | `.taylor_spec`, `.taylorN_spec` use the already-landed `isTaylorMap`: the residue is the constant coefficient, constants of k stay constant, and each coordinate is its residue plus its matching formal variable |
| These are the canonical Taylor maps, not arbitrary maps | `.taylor_unique` and `.taylorN_unique` assert uniqueness among all ring homomorphisms with that characterization |
| A vector phi in (W)L[[W]]^r | `.phi`, `.phi_zero`; over a field the zero-constant condition is membership in the variable ideal, including m=0 |
| The specified graph on N | `.phi_value` is the Taylor expansion of the restricted y-coordinate minus its residue constant. No lift of a residue constant into the original local ring is assumed |
| h_b(W,phi)=0 and uniqueness | `.solution` and `.unique_solution`, using the actual `MvPowerSeries.subst` and `implicitGraphVariables` |
| h_b = U_b(Y-phi), with U_b invertible | `.matrix`, `.matrix_unit : IsUnit matrix`, and `.factorization`, with entries in L[[W,Y]] |
| The invertible continuous change Y=phi+Z | `.straight` is an L-algebra equivalence; `.straight_apply` identifies its action with actual substitution, `.straight_inverse` fixes its inverse to the negative shift, and both continuity fields use the coefficientwise topology with discrete L |
| The extended ideal of N becomes (Z) | `.ideal_of_N` identifies the kernel of the actual stalk map with the h-germ ideal, and `.ideal_straight` sends that extended kernel ideal to the span of the transverse formal variables |
| Coordinate derivatives stay regular on the same open | `ImplicitCoordinateDerivations.deriv` gives regular derivatives on EVERY open; `.scalar`, `.coordinate`, `.restriction` and `.commute` give their coordinate normalization, k-linearity, restriction and commutation |
| Differentiation commutes with germs and Taylor expansion | `ImplicitTaylorPoint.germ_partial` and `.derivative` |
| Restriction to N agrees with evaluation on the implicit graph | `.restriction` is the equality between graph substitution of the ambient Taylor series and `taylorN` of the canonical stalk pullback |
| Arbitrary family F with infinitely many regular coefficients and finitely many T variables | `.coefficients` quantifies t, an unrestricted family `(Fin t →₀ ℕ) → B.presheaf.stalk (j b)`, gamma and delta; `implicitShiftFamily` applies actual substitution separately to every coefficient |
| The Z^delta T^gamma coefficient is Taylor_N of the restricted y-derivative divided by delta! | `.coefficients`, with `implicitTransverseCoeff` extracting the Z coefficient as a SERIES in W, `implicitIteratedDerivative` taking the regular derivative, `j.stalkMap b` restricting it, and `MvPowerSeries.C` of the inverse of `δ.prod (fun _ n => n.factorial)` implementing the scalar division |
| All these coefficients are regular on the same original neighborhood | For any common open U the input family may be its germs; `germ_partial` identifies each iterated derivative with the germ of `D.deriv U`. Thus the right side is the Taylor expansion of an actual derivative section on U restricted to N. No intersection of infinitely many smaller opens is used |
| Residue-field extension | `.extension_unique` and `.extension_taylorN_unique` compare the canonical maps; `.extension_phi` gives existence and uniqueness of the coefficientwise image of phi; `.extension_matrix` gives the invertible mapped matrix and factorization; `.extension_substitution` and `.extension_coefficients` state the substitution and factorial identities over the target field |
| Arbitrary coefficient-field sizes | These extension fields quantify `K : Type v` independently of the scheme universe. The three coordinate/residue equations are written out for K because the existing `isTaylorMap` interface puts its three rings in the same universe; this avoids an extra universe equality |
| The local Taylor map is faithfully flat, also at nonclosed points | `.faithfullyFlat` states `RingHom.FaithfullyFlat` for the actual local map. The main theorem additionally gives the uniquely characterized faithfully flat local Taylor map at EVERY x of B, independently of h |
| Equality of extended finitely generated ideals implies equality of stalk ideals | `.ideal_descent`, also explicitly present at every ambient x in the main theorem |
| Equality of stalks of two coherent ideals extends to a neighborhood | `.coherent_ideal_neighbourhood` uses `Scheme.Modules.IsQuasiCoherentFiniteType I.toModules` and the same for J; its premise is equality of their sets of affine-neighborhood germs, precisely equality of their ideal stalks; its conclusion is equality `I.comap U.ι = J.comap U.ι` on an open U containing x |

The continuity convention is explicit in the type, using
`MvPowerSeries.WithPiTopology.instTopologicalSpace` with the discrete topology on L.
For finitely many variables this is the (W,Y)-adic topology. No file-local instance,
notation, abbreviation or private copy is needed to read the public declarations.

The completion convention in the node is retained through the existing Taylor-map
characterization, with uniqueness stated explicitly. The centered diagonal-completion
construction in step 3 has exactly those coordinate and residue values and therefore
is exactly the map specified here. It is not an identification of the original
local completion with L[[W,Y]]. In particular all m+r variables survive at a
generic point. The proof docstring spells out extension to L, the diagonal ideal,
the canonical finite quotients, and their inverse limit.

Field-extension comparisons are coefficientwise on the Taylor expansions of original
regular germs. On the actual base-changed chart these are precisely the restrictions
of its K-linear Taylor maps; the tensor-product universal property then determines
the maps on the base-changed local rings. No assertion identifies the ordinary tensor
product of power-series rings with a completed power-series ring.

Dependencies read and used:

- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, with its genuine
  coefficient-family ring structure; `Substitution`: `MvPowerSeries.subst`,
  `substAlgHom` and their substitution conditions; `Rename`: `rename`.
- `Mathlib.RingTheory.MvPowerSeries.Derivative`: `MvPowerSeries.pderiv`, whose
  coefficient formula is coefficient(d+e_i) times (d_i+1).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `FiniteType`: `LocallyOfFiniteType`; `QuasiCompact`: `QuasiCompact`;
  `Etale`: `AlgebraicGeometry.Etale`. Their full affine-local signatures and
  docstrings were read. The theorem retains the source's separate smoothness
  and finite-type hypotheses even though the chart implies local smoothness.
- `Mathlib.Algebra.Field.Defs`: `Field`; characteristic zero is `CharZero`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`,
  `Γevaluation`, and the functorial residue/stalk maps.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion`
  and its canonical map. These support the source construction in the proof plan;
  the statement uses actual scheme stalks and their uniquely characterized maps.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AffineSpace` and its polynomial-spectrum
  identification. The statement uses polynomial spectra for the coordinate morphisms.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `D`,
  `linearMapEquivDerivation`. The coordinate derivations are the duals to the
  differential basis, as written in the proof docstring.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `Scheme.Modules.IsQuasiCoherentFiniteType`, exactly quasi-coherent plus finite type;
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies the
  canonical `IdealSheafData.toModules` and its inclusion.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`, and
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- The added landed dependency `Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum`:
  `HilbertCoefficient.isTaylorMap`. Its full signature/docstring and definition were
  read; the notion is reused rather than defined again.
- The added landed dependency `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`:
  `Scheme.Hom.ker` and `Scheme.IdealSheafData`. The existing `.Subscheme` and
  `.Functorial` APIs provide the zero subscheme, its inclusion and pullback of ideals.

The stated proof-dependency modules are imported without `public`, including the
prescribed-coordinate differential criterion, augmented-etale associated-graded
comparison, etale/smooth comparison, finite-type closed support, formally-etale
lifting, polynomial differential basis, flatness, completion and affine-local
ring-map comparison modules. Definitions used by the statement are public imports.

Edge cases checked mathematically:

- r=0: determinant is 1, the Jacobian open is B, N=B, the graph is empty and the
  substitution is the identity. The empty matrix is a unit in its one-element ring.
- m=0: the W-series ring is L and zero constant forces phi=0; N is etale of
  relative dimension zero. No positive-dimension assumption is made.
- t=0: the formal family has its one constant multi-index; the formula specializes
  to a single regular function. delta=0 gives ordinary restriction with factorial 1.
- Empty B has no center a and no points; the coordinate-derivation construction and
  universal conclusions on opens are still meaningful, including the zero section ring.
- For h=y-w^2 at the origin, phi=W^2. For c=y^2 the Z coefficient is 2W^2 and the
  Z^2 coefficient is 1, exactly the derivative/factorial expression on N.
- At the generic point of A^1_k the ambient map is k(t) -> k(t)[[W]], t -> t+W.
  The domain is its actual field stalk and the formal variable is retained. This
  is faithfully flat, unlike a mistaken claim that its completion supplies a parameter.
- For char p the delta! division fails in general (use y^p); char zero is retained.
- Nonclosed points, nontrivial residue-field extensions, arbitrarily large target
  coefficient fields and nonaffine B are all included. No closed-point or rational-point
  assumption is introduced. The point of B_L used by the completion proof is rational
  over L, as required by the node, not assumed rational over k.
- Ideal equalities concern the span/kernel ideals, not their radicals or zero sets.
  Finite generation is explicit in ideal descent, and coherence in the neighborhood
  conclusion is the exact recorded finite-type notion.

Searches actually run:

- `msearch.py ... leansearch "An etale coordinate chart of a smooth scheme in characteristic zero has regular partial derivatives commuting with its faithfully flat Taylor expansion and implicit formal coordinate substitutions."`:
  eight hits for etale implies smooth, formal etaleness and standard smoothness.
  These are component inputs, with some outdated search-index aliases; none states
  the implicit coefficient calculus. Actual current declarations were read locally.
- `msearch.py ... leanfinder "Etale coordinates smooth scheme Taylor power series implicit function regular coefficient partial derivative faithfully flat Taylor map"`:
  eight hits, including `Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial`
  and standard-etale presentations. They supply neither the implicit substitution
  nor the coefficient-family and nonclosed-point descent assertions.
- `msearch.py ... loogle "MvPowerSeries.subst, MvPowerSeries.pderiv, RingHom.Etale"`:
  zero hits for the combined query; the component APIs were then read directly.
- `msearch.py ... grep "isTaylorMap|implicit.*[Tt]aylor|[Tt]aylor.*[Ff]lat"`:
  zero Mathlib hits.
- `msearch.py ... grep "Taylor|taylor|implicit|[Cc]oordinate" RingTheory/MvPowerSeries`:
  zero hits. Direct source reads found Mathlib's actual substitution and differentiation
  APIs but no etale-coordinate calculus theorem.
- `rg` over `lean/WeilConjectures`, including the exact item id: no declaration of
  this theorem. The nearby `PopescuDesingularizationSubstitution` is a first-order
  polynomial expansion, not this theorem.
- `rg` over `lean/Sheaf` found `RegularHilbertCoefficientDatum.isTaylorMap` and the
  downstream `RegularHilbertCoefficientData` proof docstring. The former is reused;
  the latter cites this item as an input and does not state its calculus.
- Direct Mathlib/source search for ideal-stalk definitions found private proof lemmas
  using sets of affine germs, and the canonical public ideal-sheaf/module bridge.
  The statement uses that bridge and writes equality of germs directly, rather than
  introducing a competing public ideal-stalk definition.

Source check: I read ILO VIII 2.3.11 and 2.3.13 at printed pp.93--94 (PDF pages
99--100). They are desingularization context, not a direct statement of this
calculus. The node already records the detailed algebraic argument as agent-written;
that argument, not a falsely attributed black box, is reproduced in the theorem's
proof docstring. I also read the local Stacks source for 0H1D, 0H93, 00RX and
00MC, matching infinitesimal quotients, differential base change, polynomial
coordinate basis and faithful flatness of the Noetherian local completion.
The missing Bierstone--Milman PDF was already recorded as WANTED by Q77; no claim
is made here to have read that unavailable local document.

No statement correction or disputed mathematical claim was needed. Q77's earlier
merged delivery was a stage-1 split and contained no Lean record; it did not
complete this stage-2 task.

Validation: the module was checked with the prescribed `scompile.py`, both under
its sandbox name and its final library module name, without errors or warnings.
The required `deliver2.py --no-push` printed OK: commit `0cce6239a51` passes
preflight and compiles. The final push is performed by `deliver2.py`.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
