## Worker report

The delivery states `AlgebraicGeometry.proj_polynomial_twist_chart` in
`Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart`. Its only proof is `sorry`.
The definition in the dependency module has fully specified data and uses the
existing `Proj.twist`, not a fresh construction of a sheaf.

The following matches every hypothesis and clause of the item.

- A commutative ring: `(A : Type u) [CommRing A]`, with unrestricted universe `u`.
  No nontriviality, Noetherianity, domain or characteristic hypothesis is added.
- m ≥ 0: `(m : ℕ)`. The coordinates are indexed by `Fin (m + 1)`.
- S with its total-degree grading: `MvPolynomial.homogeneousSubmodule
  (Fin (m + 1)) A`, local notation `𝒜`, with local `MvPolynomial.gradedAlgebra`.
- P: the recorded Mathlib `AlgebraicGeometry.Proj 𝒜`, local notation `P`.
- U_k: the recorded `Proj.basicOpen 𝒜 (MvPolynomial.X k)`, local notation `U k`.
- The twisting module and its named local bases: `Proj.polynomialTwist A m 1`
  specializes the existing `Proj.twist`; `E k` is the existing
  `Proj.twistPowSection 1 (MvPolynomial.isHomogeneous_X A k)`, the fraction x_k/1.
- Cover: `(⨆ k : Fin (m + 1), U k) = ⊤`.
- Each chart is canonically Spec S_(x_k): `IsIso (Proj.basicOpenToSpec 𝒜
  (MvPolynomial.X k))`. This is the canonical map to the spectrum of
  `HomogeneousLocalization.Away 𝒜 (MvPolynomial.X k)`, not an arbitrary isomorphism.
  Its `asIso` is Mathlib's recorded `Proj.basicOpenIsoSpec`.
- The prescribed polynomial map is an A-algebra isomorphism: there exists an
  `e : MvPolynomial {l : Fin (m + 1) // l ≠ k} A ≃ₐ[A] Away ...` with
  `e (MvPolynomial.X l) = MvPolynomial.awayXRatio A k l.1` for every l.
  Because an algebra homomorphism from a polynomial algebra is determined by
  its variables, this is precisely the map in the node, including its constants.
- Each named basis is a basis of the free rank-one restriction:
  `Scheme.Modules.IsFreeGenerator (M := Proj.polynomialTwist A m 1) (E k)`.
  The definition quantifies over all smaller opens, not merely global sections.
- e_l = (x_l/x_k)e_k on the overlap: the fifth conjunct restricts `E l` and `E k`
  by the presheaf maps from U_l and U_k to `U k ⊓ U l`. The scalar is the
  restriction of `Proj.awayToSection 𝒜 (MvPolynomial.X k) (awayXRatio A k l)`.
- The intersection is the basic open of x_l/x_k in U_k: the sixth conjunct is
  the preimage of U_l under `Proj.awayι` equal to `PrimeSpectrum.basicOpen
  (awayXRatio A k l)`. This uses the canonical identification of U_k with Spec
  of the localization, so states exactly the intersection clause.
- Unique structure morphism: `∃! q : P ⟶ Spec (.of A), ...` with each
  `awayι ... ≫ q = Spec.map (CommRingCat.ofHom (algebraMap A (Away ...)))`.
  The algebra instance from the upstream homogeneous-localization extension
  sends a to the constant polynomial a divided by 1; its formula was read in
  `WeilConjectures/Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:80`.
  Thus this equality states exactly every local restriction required by the node.

Dependency declarations read and used:

- def-pc-proj: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme,
  `AlgebraicGeometry.Proj` (855) and `projIsoSpec` (847); Mathlib's
  ProjectiveSpectrum.Topology `ProjectiveSpectrum.basicOpen` (332).
  `Proj.basicOpenToSpec`, `basicOpenIsoSpec` and `awayι` were read in
  Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic (138, 161, 186).
- def-nagata-homogeneous-localization-degree-zero:
  Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization,
  `HomogeneousLocalization.Away` (601), with its `Away.mk` signature and docstring.
- def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec` (470) and `Spec.map` (479).
- def-pc-projective-space-twist: the recorded
  WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist,
  `AlgebraicGeometry.ProjectiveSpace.twist` (105), was read in full with its
  docstring and its TODO. Its usable polynomial counterpart
  `AlgebraicGeometry.Proj.twist` (ProjectiveSpectrum.Twist:382),
  `Proj.twistPowSection` (655), `Proj.isFreeGenerator_twistPowSection` (683),
  and `Proj.map_unitToTwist_eq_smul` (508) were read. The dependency repair is below.

Source: the local literature checkout contains the lists but not constructions.tex;
read the Stacks pages [01NG](https://stacks.math.columbia.edu/tag/01NG),
[01M4](https://stacks.math.columbia.edu/tag/01M4),
[01ME](https://stacks.math.columbia.edu/tag/01ME), and
[01MS](https://stacks.math.columbia.edu/tag/01MS). The node remains unchanged.
The docstring spells out all eight steps, naming the node used by each step.

Edge cases checked: m=0 gives one variable and a polynomial algebra on the empty
subtype of other variables (A itself); k=l makes the scalar one and the basic open
the entire chart; A the zero ring gives empty spectra and the unique empty-scheme
morphism; arbitrary characteristics and zero divisors are allowed. No positivity
assumption is made on m. All variables and universes are explicitly bound (A and m are section variables). There are no
`let` binders in the statement, no hollow hypothesis and no disputed statement.

Searches actually run with msearch.py for group F1 and this item:

- LeanFinder: "standard charts of Proj of a polynomial ring over a commutative ring
  and twisting sheaf generators transition x_l/x_k": eight Mathlib hits, including
  Proj.awayι, awayToSection, basicOpenIsoAway_hom and basicOpenToSpec_app_top;
  no combined polynomial-and-twist chart statement.
- Loogle: "AlgebraicGeometry.Proj.basicOpenIsoSpec,
  AlgebraicGeometry.Proj.twistPowSection": no hit; the service reports unknown
  identifier Proj.twistPowSection (an upstream-project declaration, not Mathlib).
- Grep: "dehomogen|twistPowSection|basicOpenIsoSpec" in
  AlgebraicGeometry/ProjectiveSpectrum: seven chart-related Mathlib hits and
  no combined statement or twisting module.
- LeanSearch: "standard polynomial projective spectrum charts twisting module
  structure morphism": unavailable, Internal Server Error; not recorded as no match.
- Direct rg over upstream WeilConjectures/AlgebraicGeometry for the item id,
  dehomogen, map_unitToTwist_eq_smul, twistPowSection and
  projectiveSpaceOverAffineToSpec found the general twisting and chart interfaces,
  including the polynomial dehomogenization isomorphism in the imported extension;
  no declaration for the combined node. Direct rg over lean/Sheaf for Proj.twist,
  dehomogen and Polynomial.*Chart found no matching declaration. Name searches
  for polynomialTwist and proj_polynomial_twist_chart over Mathlib, upstream,
  and lean/Sheaf found no collisions.

## Dependency modules

`def-pc-projective-space-twist` receives
`Sheaf.AlgebraicGeometry.PolynomialProjectiveTwist`, defining
`AlgebraicGeometry.Proj.polynomialTwist`. Its former record is unusable here:
`ProjectiveSpace.twist n (Spec A) d` lives on the base-change construction,
whereas both the dependency node and this item's statement name the polynomial
Proj directly. The former module explicitly lists the comparison with polynomial
Proj as a TODO. The repair is the exact polynomial specialization of the existing
`Proj.twist`, whose data are sections of the degree-d localization sheaf; it does
not copy that construction. `Proj.twistPowSection d` supplies the bases x_i^d;
the upstream free-generator and multiplication formulas yield the prescribed
transition rule. These local trivializations also identify this degree-part
construction with the node's glued free rank-one modules and show invertibility.
Only the dependency's lean record is changed, with the reason in lean.note.

## Second reading by F1

I independently read the item node, its Stacks source places, and both delivered modules. The
objects and hypotheses match item by item: `A : Type u` with `[CommRing A]`, `m : ℕ`, the
homogeneous total-degree algebra `𝒜` on `Fin (m+1)`, `P = Proj 𝒜`, and `U k = D₊(X k)`.
No Noetherian, domain, nonzero, characteristic, or universe restriction is added. The first
conclusion conjunct is the cover `⨆ k, U k = ⊤`; the second gives the canonical
`Proj.basicOpenToSpec` isomorphism property; the third quantifies the stated A-algebra
isomorphism and sends each other variable to `MvPolynomial.awayXRatio`. The fourth says the
existing polynomial `Proj.twist` specialization has the named `twistPowSection` free generator.
The fifth states the restriction transition `e_l = (x_l/x_k) • e_k` with the actual presheaf
maps, and the sixth identifies the inverse image of `U l` with
`PrimeSpectrum.basicOpen (x_l/x_k)`. The final existential-universal clause is the unique
structure morphism to `Spec A`, with every chart restriction induced by `a ↦ a/1`.
Quantifier order and all six conjunction clauses are preserved verbatim in the Lean theorem.

The dependency module `PolynomialProjectiveTwist` was also read against
`def-pc-projective-space-twist`: it defines `Proj.polynomialTwist` as the existing `Proj.twist`
on the polynomial homogeneous algebra, with no `sorry` data or duplicate sheaf construction.
The old recorded `ProjectiveSpace.twist` is a base-change model and therefore was unusable for
this dependency; the node record and report explain that repair.

Edge cases checked are `m = 0` (one chart and the empty-variable polynomial algebra), `k = l`
(ratio one and the whole chart intersection), zero rings (possibly empty spectra), arbitrary
characteristic and zero divisors, and unrestricted ring universe. No `let` binders or unbound
variables occur.

I searched Mathlib, the source repository, and `lean/Sheaf` by name and concept using
LeanFinder, Loogle, grep, and direct `rg`; only the existing Proj chart, homogeneous
localization, and twist primitives were found, with no combined statement. The Stacks tags
01NG, 01M4, 01MB, 01ME, and 01MS were opened directly. The only mismatch found was the
unusable dependency record described above; I changed its module and `lean.note`, while leaving
the item's statement unchanged. Both modules compile together with `scompile.py` and contain
only the permitted statement `sorry`.

## Reviewer fix (R-ptc1354, stage 2)

- The dependency module `Sheaf.AlgebraicGeometry.PolynomialProjectiveTwist` (`Proj.polynomialTwist := Proj.twist _ d`) was a thin restatement of the source's `Proj.twist` and re-recorded def-pc-projective-space-twist, a node landed and recorded by L at `ProjectiveSpace.twist` (used by landed modules, e.g. AmpleImmersionAffineBase, ProjectiveLinePowerAffineCharts). One definition per notion: the node is reverted (`--revert-nodes def-pc-projective-space-twist`) and the module left out.
- The item now uses the source's `Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) A) 1` directly (no new definition): the node names P = Proj(A[x_0..x_m]) with D_+(x_k) and S_(x_k), which is the Proj model, of whose integral form `ProjectiveSpace.twist` is the pullback; the comparison is the source's TODO (stage 3).
- The section variables `A`, `m` are bound in the theorem and the file-local notations (𝒜, P, U, E, r) are written out, so the recorded statement is self-contained.
- Every clause otherwise unchanged; recompiled with `SHEAF_GROUP=L tools/lean_file.sh` (clean). Checked that `IsIso (Proj.basicOpenToSpec …)` is not an instance (the clause is not vacuous).
