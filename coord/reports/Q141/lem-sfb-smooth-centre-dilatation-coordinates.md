## Worker report

The module `Sheaf.RingTheory.SmoothCentreDilatationCoordinates` states
`Algebra.smooth_centre_dilatation_coordinates`, with its sole proof `sorry`.
The node's mathematical statement, dependencies and proof are unchanged. No
new definition or dependency module is required: the ideal, fraction
subalgebra, quotient, basis and differential map use existing Mathlib
constructions directly. No definition data is postponed.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| R is a DVR | `R : Type u`, `[CommRing R] [IsDomain R] [IsDiscreteValuationRing R]` |
| π is a uniformizer | `(π : R) (hπ : Irreducible π)`; `IsDiscreteValuationRing.irreducible_iff_uniformizer` identifies this with generating the maximal ideal |
| r,n ≥ 0 | `(r n : ℕ)`, including zero |
| C is a commutative R-algebra | `C : Type u`, `[CommRing C] [Algebra R C]` |
| Images of y and z | `(y : Fin r → C) (z : Fin n → C)` |
| Étale coordinate chart | `hEtale` is scheme `Etale` of `Spec.map` of `MvPolynomial.aeval (R := R) (Sum.elim y z)` |
| J = (π,z₁,…,zₙ) | `J : Ideal C`, `hJ : J = Ideal.span ({algebraMap R C π} ∪ Set.range z)` |
| C[J/π] inside C[1/π] | `C' : Subalgebra C (Localization.Away (algebraMap R C π))`, with `hC'` identifying it with `Algebra.adjoin C {x | ∃ b ∈ J, x = algebraMap ... b * IsLocalization.Away.invSelf ...}` |
| Presentation isomorphism over C | `e : (MvPolynomial (Fin n) C ⧸ Ideal.span (Set.range (fun j => C π * X j - C (z j)))) ≃ₐ[C] C'` |
| Canonical map tⱼ ↦ zⱼ/π | The first two conjuncts identify `e (Ideal.Quotient.mk _ (MvPolynomial.X j))` with `z' j`, then identify its coercion into the actual localization with `z j` times the inverse of π |
| New coordinate chart is étale | Third conjunct: scheme `Etale` of `Spec.map` of the R-polynomial evaluation at the old y-images and the specified `z'` |
| Smooth over R | Fourth conjunct: `AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (algebraMap R C')))` |
| Flat over R | Fifth conjunct: `AlgebraicGeometry.Flat` of that same structure morphism |
| Noetherian | `IsNoetherianRing C'`, the standard equivalent of finite generation of every ideal |
| C'[1/π] = C[1/π] | `IsLocalization.Away (algebraMap R C' π) (Localization.Away (algebraMap R C π))`; its algebra map is the subalgebra inclusion, so this is the canonical identification rather than existence of an unrelated ring equivalence |
| Differential module free on dy,dz' | Existential `b : Module.Basis (Fin r ⊕ Fin n) C' (KaehlerDifferential R C')`, with both families of basis-vector equalities to `KaehlerDifferential.D` |
| Canonical differential map on dy | `KaehlerDifferential.mapBaseChange R C C' (1 ⊗ₜ[C] D R C (y i)) = b (Sum.inl i)` |
| Canonical differential map on dz | Same existing map, with input `1 ⊗ₜ[C] D R C (z j)`, has value `algebraMap R C' π • b (Sum.inr j)` |

`J,hJ` and `C',hC'` name fully specified constructions using equality
binders because local `let` statements are forbidden. They add no geometric
condition: the equalities have their literal construction as a witness for
every input. The isomorphism is a C-algebra isomorphism, so it fixes all
coefficients; the polynomial generators determine it uniquely. The `z'`
elements are uniquely determined by their coercions into the localization.
The theorem introduces no arbitrary substitute for a canonical map.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`:
  `IsDiscreteValuationRing`, `IsDiscreteValuationRing.irreducible_iff_uniformizer`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`:
  `AlgebraicGeometry.Etale`.
- `Mathlib.Algebra.MvPolynomial.Basic` and `.Eval`:
  `MvPolynomial`, `MvPolynomial.aeval`, `MvPolynomial.algHom_ext`.
- `Mathlib.AlgebraicGeometry.Scheme`:
  `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`.
- `Mathlib.GroupTheory.MonoidLocalization.Away` and
  `Mathlib.RingTheory.Localization.Away.Basic`:
  `Localization.Away`, `IsLocalization.Away`, `IsLocalization.Away.invSelf`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`:
  `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`:
  `AlgebraicGeometry.Flat`.
- `Mathlib.RingTheory.Kaehler.Basic`:
  `KaehlerDifferential`, `.D`, `.linearMapEquivDerivation`, `.mapBaseChange`.

The stated proof-dependency modules are imported privately, including
`WeilConjectures.RingTheory.EtalePolynomialStandardSmooth` for
`Algebra.isStandardSmooth_of_etale_polynomial`. The other private imports
supply the recorded tensor product, flat torsion-freeness, formally étale
Kähler base-change, polynomial Kähler basis, smooth-flat,
standard-smooth/smooth, finite-type Noetherian, and affine ring-property
bridges. I read these declarations as well as the statement-dependency
signatures and docstrings. Imports shared by statement and proof use public
visibility. No dependency-record repair is needed.

Edge cases checked before writing:

- n = 0: J = (π), adjoining its fractions changes nothing; the zero-variable
  polynomial quotient is C, and there are no normal-coordinate formulas.
- r = 0: there are only normal-coordinate vectors and their π coefficients.
- r = n = 0: the basis has empty index, agreeing with vanishing relative
  differentials for an étale R-algebra.
- C is the zero ring: no `Nontrivial C` was imposed; quotient, localization,
  scheme properties on the empty spectrum, and the basis over the zero ring
  remain valid.
- π becomes a unit in C: the subalgebra is all of C[1/π] and identifies with
  C; no condition excluding a chart with empty special fibre was imposed.
- π cannot be zero in R, by the DVR uniformizer condition, but need not stay
  a nonunit in C. No assumption of an R-point or nonempty special fibre occurs.
- The common universe u is the standard same-universe encoding required by
  Mathlib's scheme morphisms; all variables and universes are explicit and
  `autoImplicit` is disabled.

Searches for an existing declaration:

- `msearch.py ... leanfinder "Etale coordinate dilatation C[t] modulo pi t
  minus z embeds in C localized away pi and has differential basis dy d(z
  divided by pi)"`: eight standard-étale-presentation hits; none states this
  coordinate dilatation presentation and its differential formulas.
- `msearch.py ... loogle "Algebra.Etale, KaehlerDifferential"`: zero hits.
- `msearch.py ... grep "dilatation|dilatate|dilatations"`: zero Mathlib hits.
- `rg -n 'dilatation|Dilatation' lean/Sheaf lean/WeilConjectures`:
  no existing construction or theorem; exact node-id and proposed theorem-name
  searches in the upstream source also found none.
- DAG text search found the parent dilatation chain and this node, with no
  existing Lean declaration for this precise statement. Existing general
  adjoin, quotient, localization and differential definitions suffice, so no
  independent missing notion or new DAG definition was introduced.

Source check: opened the primary BLR scan at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf,
PDF pages 68–70 and 74–76. The affine fraction chart and smooth-coordinate
argument agree with the node. The differential comparison uses the same
rescaling of normal coordinates. The node's six proof steps are included in
the theorem docstring. No mathematical statement correction or dispute.

Validation: the prescribed server compile passed both sandbox and actual
library module (2.3 s and 2.5 s), with no errors or warnings. An earlier
polynomial coefficient inference error was repaired by spelling out `(R := R)`
at both coordinate evaluation maps. Every delivered line is at most 100
characters. Only the item's `lean` field is changed in its node copy.

## Second reading by Q141

I reread the completed file against the node clause by clause in the table
above. This is a worker self-audit; no second agent was started, as the brief
prohibits delegation and assigns independent review to the maintainer.
The review specifically checked that `e` fixes C, its variables map to the
actual fractions, the localization clause uses the actual subalgebra
inclusion, and the differential formulas use Mathlib's canonical
`mapBaseChange`. Both coordinate charts explicitly use R as coefficient ring.
The zero-ring and empty-coordinate cases are retained. No mismatch remains
in this self-audit; the maintainer's independent review is still required.
