## Worker report

The module `Sheaf.RingTheory.GeometricFittingDepthDescent` states
`Algebra.geometric_fitting_depth_descent`, with one named theorem and its proof `sorry`.
There are no new definitions, new nodes, dependency repairs, or statement corrections.
The original node is unchanged except for its `lean` record.

I read Stacks `curves.tex`, Tag 0C4D, label `lemma-nodal`, including the arbitrary-field
paragraphs about the first-Fitting closed subscheme, geometric reducedness, separability,
flat descent of depth one, and the converse. The nine-step proof plan in the module follows
all nine steps of the accepted DAG split, including completion. No curve-dimension
hypothesis is added: the isolated geometric field stalk of the singular quotient and
the stated depth hypothesis are exactly the inputs used by this algebraic descent step.

Hypotheses and objects, matched individually:

- The fields are `(k : Type u) (Ω : Type v) [Field k] [Field Ω]`; the extension and its
  algebraic-closure property are `[Algebra k Ω] [IsAlgClosure k Ω]`.
- `S : Type w`, `[CommRing S] [Algebra k S] [Algebra.FiniteType k S]` express the finite
  type algebra. This is the Algebra-instance form of the dependency's recorded
  `RingHom.FiniteType` (see `RingHom.finiteType_algebraMap`), not a different definition.
- `(p : Ideal S) [p.IsMaximal]` is the given maximal ideal. The given geometric prime
  is `(q : PrimeSpectrum (S ⊗[k] Ω))`. Its contraction condition is exactly `hq`.
- `A` is always `Localization.AtPrime p`, and `B` is always
  `Localization.AtPrime q.asIdeal`. The maximal ideals are `IsLocalRing.maximalIdeal`
  of these rings, equal to the extensions of `p` and `q.asIdeal` by
  `Localization.AtPrime.map_eq_maximalIdeal`. `F` is `S ⧸ p` throughout.
- The notation `J = Fit_1(Ω[S/k])` is rendered by `π.presentationFittingIdeal 1`, where
  `π : (Fin d → S) →ₗ[S] KaehlerDifferential k S` and `hπ` make `π` an arbitrary finite
  generating surjection. The geometric Fitting ideal uses an independently arbitrary
  finite generating surjection `ρ` with proof `hρ`. These are representations of the
  already-defined ideals, not finite-presentation or extra freeness assumptions on
  the differential modules or their kernels. Such presentations exist for finite type
  algebras; the recorded independence theorem identifies every choice. The case `d=0`
  or `e=0` remains allowed.
- The geometric differential module is
  `@KaehlerDifferential Ω (S ⊗[k] Ω) _ _ Algebra.TensorProduct.rightAlgebra`.
  This uses exactly the node's tensor order and the structural map `a ↦ 1 ⊗ a`.
  No unrelated Ω-algebra action is quantified or silently inferred.
- `J_A` is `Ideal.map (algebraMap S (Localization.AtPrime p))
  (π.presentationFittingIdeal 1)`. `J_B` is the corresponding `Ideal.map` for `ρ` and
  the localization map to `B`. The hypothesis `hfit` is precisely `J_B = n`.
- `hdepth` is `IsLocalRing.depth (R := B) B = 1`. No flatness, separability,
  Noetherianity, dimension, reducedness or completeness assumption is added.

Conclusions, matched individually:

- `Module.Finite k (S ⧸ p)` is finiteness of the residue field extension.
- `Algebra.IsSeparable k (S ⧸ p)` is separability, with algebraicity built into this
  recorded Mathlib definition. Together these are finite separability of `F/k`.
- The next equality says exactly `J_A = IsLocalRing.maximalIdeal A`.
- `IsLocalRing.depth (R := A) A = 1` is depth one of the original local ring.
- The completion is `AdicCompletion (IsLocalRing.maximalIdeal A) A`. Its displayed
  ideal-depth equality is depth one for `(maximalIdeal A)` extended along its canonical
  algebra map. This is precisely ring depth of the completion:
  `AdicCompletion.maximalIdeal_eq_map` identifies that ideal with its maximal ideal,
  and `IsLocalRing.depth` is defined as ideal depth at the maximal ideal. The required
  Noetherianity follows from finite type over the field and localization. Using this
  ideal-depth form avoids placing a derived Noetherian instance in the statement.
- The final existential gives `E : A/J_A ≃+* S/p`, together with
  `E.toRingHom.comp (Ideal.Quotient.mk J_A) =
  (IsLocalization.AtPrime.equivQuotMaximalIdeal p A).symm.toRingHom.comp
  (IsLocalRing.residue A)`. Thus it is the isomorphism induced by the actual residue
  map, not an uncharacterized isomorphism. The equality also implies compatibility
  with the original scalar maps.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`, and
  `RingHom.finiteType_algebraMap`; the first is explicitly defined through the second.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, its local
  structure, `IsLocalization.AtPrime.equivQuotMaximalIdeal` (full definition and
  signature read), and the maximal-ideal identification. The companion recorded
  residue/fibre definitions were read in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and `.Fiber`.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and its
  actual compatible-sequence data and algebra structure.
- `WeilConjectures.RingTheory.Depth`: `Ideal.depth` and `IsLocalRing.depth`, including
  the infinity branch and the supremum over regular-sequence lengths.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `KaehlerDifferential.D`
  and `KaehlerDifferential.linearMapEquivDerivation`, including their docstrings.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal` and
  `LinearMap.presentationFittingIdeal_independence_baseChange`, including the
  convention `n ≤ k`, full arbitrary-base-change signature, and proof plan.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure` and `.Basic`: the recorded
  algebraic-closure interface `IsAlgClosure` with its algebraic and algebraically
  closed conditions (the dependency is a Mathlib leaf and needs no Lean-record repair).
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`;
  `Mathlib.RingTheory.TensorProduct.Basic`: `Algebra.TensorProduct.rightAlgebra`,
  whose explicit definition is the right-factor structural action.
- `Mathlib.FieldTheory.Separable`: `Algebra.IsSeparable`, its full signature and
  docstring explicitly including algebraicity.

The plain imports include the stated proof dependencies: differential tensor base
change, tensor right exactness, `Algebra.geometric_field_stalk_descent`, regular
sequences, `IsLocalRing.depth_eq_add_of_flat_local`, local completion,
`AdicCompletion.isNoetherianRing`, and flatness of completion. The proof-only node
`lem-trf-separable-evaluation-local-base-change` has no recorded declaration in this
read snapshot, so there is no module of that node to import; its use is retained in
the proof docstring and unchanged DAG proof plan. It is not a statement prerequisite.

Edge cases checked before writing:

- The zero algebra admits no maximal ideal, so it supplies no inadmissible zero residue
  field or local ring. No extra `Nontrivial S` hypothesis is imposed.
- For zero or one differential generator the index-1 ideal is the unit ideal by the
  dependency's convention; `hfit` then cannot hold for a proper local maximal ideal.
- A smooth point has unit first Fitting ideal, so the geometric ideal hypothesis fails.
- A nodal algebra `k[x,y]/(xy)` at the origin has first Fitting ideal `(x,y)` and depth
  one, including characteristic two, and satisfies all the stated conclusions.
- An inseparable residue extension cannot have the reduced geometric field stalk of
  `S/J` forced here. No perfectness or characteristic restriction is added.
- Fields have depth zero rather than one. The completion is taken at the original
  maximal ideal and its depth is in the same `ℕ∞` as the original depth.
- The three object universes `u v w` are independent. There is no bounded universe of
  test fields and no hidden equality between the universes of the two fields or `S`.

Searches actually run for this delivery:

- `msearch.py ... leanfinder "Descent of first Fitting ideal of Kahler differentials
  and depth one from algebraic closure to local ring"`: 8 hits, including formally
  smooth cotangent comparisons, unramified loci, and a cotangent-space generator
  bound. None is this Fitting-and-depth descent theorem.
- `msearch.py ... loogle "KaehlerDifferential, Algebra.IsSeparable"`: 0 hits.
- `msearch.py ... grep "Fitting|fittingIdeal|fitting_ideal" RingTheory`: 2 hits in
  `Mathlib/RingTheory/Artinian/Module.lean`, both about Fitting decomposition of an
  endomorphism, not the presentation-minor ideal.
- `msearch.py ... leansearch "Faithfully flat local descent of maximal Fitting ideal
  of differentials and depth one"`: 8 hits about flat modules and faithful flatness,
  with no combined Fitting/depth/separability statement.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for the Fitting, geometric descent
  and depth terms found the existing presentation-ideal interface and the field-stalk
  descent theorem, but no theorem combining the conclusions of this item.
- `grep -rn "lem-trf-geometric-fitting-depth-descent" lean/WeilConjectures`: no hits.
- `rg` on the project and `dag/lean_names_upstream.json` for
  `geometric_fitting_depth_descent|GeometricFittingDepthDescent`: no declaration clash.

The prescribed `scompile.py` compiled the module both as its sandbox module and as
`Sheaf.RingTheory.GeometricFittingDepthDescent` with no errors or warnings. The file
binds every variable and universe explicitly, sets `autoImplicit false`, contains one
`sorry` theorem, and has no local definitions, notation, instances, or proof data.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
