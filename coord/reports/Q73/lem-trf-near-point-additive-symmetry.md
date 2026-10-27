## Worker report

The module `Sheaf.AlgebraicGeometry.NearPointAdditiveSymmetry` states
`AlgebraicGeometry.HilbertSamuel.near_point_additive_symmetry`, with `sorry` as its
only theorem proof. It also constructs three canonical helpers belonging to this
statement: `nearPointResidueAlgebra`, `nearPointTrdeg`, and `nearPointFibreIdeal`.
Their data contain no `sorry` and require no existence choice.

The item's mathematical statement, proof, and proof dependencies are unchanged.
Its statement dependencies additionally name the already landed definition nodes
`def-trf-normal-cone-residue-fibre` and `def-trf-hilbert-samuel-invariant`, whose
existing constructions are reused. No new nodes or dependency repairs are needed.

### Source and exact hypothesis correspondence

I read the entire item and its six proof steps, all statement-dependency nodes,
the recorded declarations and their docstrings, and the relevant canonical helpers.
The source read online was Cossart--Jannsen--Saito, March 12, 2009,
https://epub.uni-regensburg.de/13766/1/MP32.pdf, printed p.36, proof of Theorem 2.14,
with Theorem 2.10(2), pp.32--33, and its reference to Theorem 2.2(2)(ii).
The characteristic-independent subgroup argument precedes the source's subsequent
linearity argument. The current blueprint ancestor is
`literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`;
it is only the ancestor, not a claim that the blueprint directly states this local algebra lemma.

| Node hypothesis or object | Lean rendering |
| --- | --- |
| F is any field | `{F : Type v} [Field F]`; no characteristic or perfection restriction |
| R is a nonzero local commutative ring | `{R : Type u} [CommRing R] [IsLocalRing R]`; `IsLocalRing` supplies `Nontrivial R` |
| R is reduced and Noetherian | `[IsReduced R] [IsNoetherianRing R]` |
| Essentially finite type F-algebra | `[Algebra F R] [Algebra.EssFiniteType F R]` |
| I is a prime ideal contained in m | `(I : Ideal R)`, `(hI : I ≤ IsLocalRing.maximalIdeal R)`, `[I.IsPrime]` |
| A=R/I is regular local | `[IsRegularLocalRing (R ⧸ I)]`, using the dependency's exact Mathlib ring clause |
| No minimal prime contains I | `hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p` |
| G=gr_I R, flat over A | `[Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]` with the recorded degree-zero algebra action |
| k=R/m | `IsLocalRing.ResidueField R`, definitionally the quotient |
| S=G tensor_A k | `Ideal.normalConeFibre I hI`, the existing canonically symmetric tensor model `k tensor_A G` |
| Y=Bl_I Spec R | `AffineBlowup I`, the existing `Proj (reesGrading I)` |
| y lies over the closed point | `(y : AffineBlowup I)` and `hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R` |
| R_y and n_y | `(AffineBlowup I).presheaf.stalk y` and its existing maximal ideal, as used by `localFunction` |
| h_y(n)=length(R_y/n_y^(n+1)) | `localFunction (AffineBlowup I) y`, using `Module.length` and its finite-length natural conversion |
| h_R(n)=length(R/m^(n+1)) | `fun n : ℕ ↦ (Module.length R (R ⧸ (IsLocalRing.maximalIdeal R) ^ (n + 1))).toNat` |
| delta=trdeg_k kappa(y) | `nearPointTrdeg I y hy`; its algebra action is constructed canonically, as described below |
| Lambda is inclusive summation | Existing `HilbertSamuel.summation` with `Finset.range (n + 1)` |
| Lambda^delta h_y=h_R | `hnear`, equality of sequences after function iteration |
| Arbitrary polynomial presentation with N degree-one variables | `(N : ℕ)` and `φ : MvPolynomial (Fin N) k →ₐ[k] Ideal.normalConeFibre I hI` |
| Surjection | `hφ : Function.Surjective φ` |
| Graded presentation, variables of degree one | `hgraded` says each `φ (X i)` belongs to the k-span of the degree-one initial classes; by the polynomial universal property this is exactly degree preservation, not minimality or linear independence |
| K homogeneous kernel | `RingHom.ker φ.toRingHom`; homogeneity follows from gradedness and is not added as an independent hypothesis |
| q_y inverse image of the original fibre-point prime | `Ideal.comap φ.toRingHom (nearPointFibreIdeal I hI y)` |

All numerical conversions are literal under the hypotheses. Noetherian local rings
have finite lengths for quotients by powers of their maximal ideals, and blowups
of Noetherian schemes are Noetherian. The blowup is of finite type over R, so the
residue extension kappa(y)/k has finite transcendence degree, even for nonclosed y.
Thus no infinite value is silently treated as zero in an admissible instance.

### Canonical constructions and fibre-point identification

`nearPointResidueAlgebra` composes only canonical maps. The inverse of
`stalkClosedPointIso (.of R)` gives an isomorphism R to the stalk of Spec R at its
closed point. `IsLocalRing.ResidueField.mapEquiv` gives the corresponding map from
k to that point's scheme residue field. `Scheme.residueFieldCongr hy.symm`
transports it to the residue field at the image of y, and the blowup morphism's
`residueFieldMap y` maps it into kappa(y). There is no arbitrary algebra instance
binder and no extra compatibility assumption.

`nearPointFibreIdeal` is the ideal span of `normalConeFibreClass I hI n a` for
exactly those a in I^n whose `reesMonomial I a.val a.property` belongs to the
homogeneous Rees prime `y.asHomogeneousIdeal.toIdeal`. The degree-n component of
Rees/m Rees is I^n/m I^n. The degree-n component of S is
I^n/(I^(n+1)+m I^n), the same quotient since I is contained in m. The products agree
on representatives. Since y maps to the closed point, its Rees prime contains
m Rees. Under this canonical quotient, the span is therefore exactly its image
prime, and its comap along φ is exactly q_y. This directly implements the node's
fibre identification without a chosen scheme isomorphism or a second copy of S.
The construction works before imposing normal flatness or the near equality.

### Every conclusion clause

| Node conclusion | Lean rendering |
| --- | --- |
| There exists an ideal L | `∃ L : Ideal (MvPolynomial (Fin N) k)` |
| L is proper | `L ≠ ⊤` |
| L is homogeneous | `∀ f ∈ L, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ L`; this is literally closure under all homogeneous components |
| L is contained in q_y | `L ≤ Ideal.comap φ.toRingHom (nearPointFibreIdeal I hI y)` |
| f(0)=0 for all f in L | `MvPolynomial.eval (fun _ : Fin N ↦ (0 : k)) f = 0` |
| f(-Z) belongs to L(Z) | `MvPolynomial.aeval (fun i ↦ -MvPolynomial.X (Sum.inl i)) f` belongs to the ideal map of L under `rename Sum.inl` |
| f(Z+W) belongs to L(Z)+L(W) | `aeval (fun i ↦ X (Sum.inl i) + X (Sum.inr i)) f` belongs to the supremum of the two ideal maps of L |
| g(Z+W) belongs to K(Z)+L(W) for all g in K | The last quantified clause, using `RingHom.ker φ.toRingHom` and the same addition substitution |
| Disjoint tuples Z,W | The larger polynomial ring has variable type `Fin N ⊕ Fin N`; the two tuple inclusions are `Sum.inl` and `Sum.inr` |
| Generated substitution ideals | `Ideal.map` of the renaming ring homomorphisms; the ideal supremum is the ideal sum |
| No degree-one generation assertion for L | No such condition is in the signature; homogeneity allows arbitrary positive degrees |

In particular neither `K ≤ L` nor a vector-subspace/linearity conclusion was added.
The formulas are equalities or ideal memberships of polynomials, not conditions
only on rational points.

### Dependency declarations used

- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (available through imports).
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`. The recorded
  `Sheaf.AlgebraicGeometry.IsRegularScheme` defines the scheme clause of that node;
  this item uses its unchanged Mathlib ring clause, not a regular-scheme predicate.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedAlgebra`, and the underlying initial-class construction.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` and `Mathlib.RingTheory.TensorProduct.Basic`:
  `TensorProduct` and its canonical commutative-ring/algebra structures, used through
  the existing normal-cone fibre; no tensor notion is restated.
- `Mathlib.RingTheory.RingHom.Flat` / `Mathlib.RingTheory.Flat.Basic`: `Module.Flat`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`.
- `WeilConjectures.Blowup.Affine.Defs`: `AffineBlowup`, `AffineBlowup.toSpec`;
  its ReesGrading import supplies `reesMonomial` and `reesGrading`.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `Proj` and the point's
  `asHomogeneousIdeal`; this point API is reused through `AffineBlowup`.
- `Mathlib.RingTheory.Length`: `Module.length`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`;
  `Mathlib.AlgebraicGeometry.Stalk`: `stalkClosedPointIso`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Basic`: `IsLocalRing.ResidueField.mapEquiv`.
- `Mathlib.Algebra.MvPolynomial.Basic`, `Eval`, and `Rename`: `MvPolynomial`,
  `MvPolynomial.eval`, `MvPolynomial.aeval`, and `MvPolynomial.rename`.
- `Mathlib.RingTheory.MvPolynomial.Homogeneous`: `MvPolynomial.homogeneousComponent`.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`: the recorded standard-grading
  interface, retained as a proof import for the presentation reduction. The given
  finite graded surjection already supplies finite degree-one generation.
- `Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes`, owned for these constructions
  by `def-trf-normal-cone-residue-fibre`: `Ideal.normalConeFibre`,
  `Ideal.normalConeFibreClass`, and its canonical ring/algebra structures.
- `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`, node
  `def-trf-hilbert-samuel-invariant`: `HilbertSamuel.summation` and `localFunction`.
- Proof-only `Mathlib.RingTheory.Localization.AtPrime.Basic`: the recorded
  `Localization.AtPrime` interface for proof step 3.

The two nondefinition proof prerequisites `lem-trf-near-blowup-order-generators`
and `lem-trf-projective-order-algebra-additive-generators` have no recorded Lean
module at the time of this delivery, so there is no such import yet. Their exact
uses are retained in the theorem's six-step proof docstring. No unstated theorem
is required to elaborate the current statement.

### Edge cases checked

- n=0: both raw lengths are 1; inclusive summation at zero remains 1 for every delta.
- delta=0: iteration is the identity, giving exactly h_y=h_R; no positive
  transcendence-degree or closedness assumption is imposed.
- Nonclosed and inseparable points: the canonical residue-field map and its
  transcendence degree require neither a k-rational point nor separability.
- I=0: the node's no-minimal-prime-containing-I assumption already excludes it;
  independently the blowup has no projective points. No extra exclusion is added.
- I=m: regularity of A is field regularity and the flatness assumption is automatic;
  the original theorem remains stated for this case whenever its other hypotheses hold.
- R a field or N=0: no relevant projective fibre point exists with such a surjective
  presentation; the statement does not insert an `N>0` hypothesis.
- K=0 and L=0 are allowed: all substitution conditions hold literally, and L=0
  is proper over the residue field. There is no requirement that L be nonzero.
- Redundant variables in a presentation are allowed: `hgraded` assumes no
  injectivity or basis property in degree one, in accord with proof step 1.
- Positive characteristic, finite and imperfect fields: all formulas are
  polynomial ideal memberships. Nothing identifies additive polynomials with
  linear polynomials or uses equality only on k-rational points.
- Field and ring universes are independent (`v`, `u`); no coefficient-field lift
  into R, finite residue extension of F, or test-object universe restriction is imposed.

### Searches and validation

All four searches were actually run with `msearch.py Q73 lem-trf-near-point-additive-symmetry`:

- `leanfinder`: `Hironaka near point blowup Hilbert Samuel equality additive subgroup normal cone equations`:
  8 results about Weierstrass preparation and power series ideals, no matching theorem.
- `loogle`: `"MvPolynomial", "IsHomogeneous"`: 12 results including
  `MvPolynomial.IsHomogeneous` and basic degree lemmas; none gives the near-point theorem.
- `grep`: `Hironaka|nearPoint|normalCone|normalConeFiber`: no Mathlib hits.
- `leansearch`: `Near point of a blowup normal cone preserved by homogeneous additive subgroup scheme`:
  8 results concerning ordinary additive subgroups/normalizers and order cones, no scheme theorem.

I also searched `lean/WeilConjectures`, `lean/Sheaf` and the DAG for the node id,
near-point names, normal-cone fibre constructions, Hilbert--Samuel functions,
Hironaka, and the proposed helper/declaration names. The existing normal-cone
fibre and Hilbert--Samuel functions were found and reused. No existing statement
or canonical exceptional-fibre-point-ideal helper duplicates this delivery.
The upstream `CompactObject` source was read because the example Sheaf module
is now withdrawn; its node records the upstream replacement.

`scompile.py` compiled both the sandbox and its library-module form cleanly.
The first attempt found a semireducible class-valued def, a redundant explicit
`Nontrivial` binder, and unavailable implicit polynomial grading. They were
repaired by `@[instance_reducible]`, using the nontriviality already supplied by
`IsLocalRing`, and writing the literal homogeneous-component closure condition.
The repaired compile exited 0, with no warnings. All universes and variables
are explicitly bound and all Lean lines have at most 100 characters.

No STATEMENT-DISPUTED issue or statement correction was needed. The published
proof docstring retains all six DAG steps; the only postponed proof is the named
item theorem. The maintainer performs the independent review after delivery.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
