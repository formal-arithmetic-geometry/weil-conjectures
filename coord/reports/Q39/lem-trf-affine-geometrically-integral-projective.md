## Worker report

Repair of returned head 4e9e75d59bf9. The previous packet supplied no stage-2 declaration.
This packet supplies `Sheaf.RingTheory.AffineGeometricallyIntegralProjective`, with
`Algebra.projective_of_geometricallyIntegral_fibres`, one theorem with proof `sorry`,
and a complete `lean` binding. It defines no new notion and proves no theorem.

The current base node was copied whole, changing only `lean`. In particular its statement,
statement dependencies, proof, proof dependencies, source and split report are retained.
This restores the scheme-interface justifications named in the return: proof step 1 and its
`uses` retain `lem-weil-pbc-fibre-product-affine-spectra`,
`lem-weil-pbc-spec-domain-stalks-function-field` and `def-pc-geometrically-irreducible`.
The module imports the Mathlib modules furnishing those bridges and gives the complete
three-step DAG proof plan in its theorem docstring. The existing proof dependency
`lem-trf-local-fibres-integral-projective` has neither a Lean binding nor a Mathlib match
in the base; no invented import or duplicate statement for it is introduced. Its use is
postponed to stage 3, not assumed as an extra hypothesis of this theorem.

The source was read in `literature/stacks-project/flat.tex`, Tag 05FT,
`lemma-fibres-irreducible-flat-projective-nonnoetherian`, including its approximation,
Noetherian-case and scalar-extension proof. The statement matches that source with the
geometric-fibre condition written out, exactly as the item's statement requests.

Clause-by-clause correspondence:

- Commutative rings `R` and `B`: `(R : Type u) (B : Type v) [CommRing R] [CommRing B]`.
  The universes are independent; neither ring is assumed nonzero, Noetherian, a field,
  local, finite, or a domain.
- The ring homomorphism `R → B`: `[Algebra R B]` supplies `algebraMap R B`.
  Every unital ring homomorphism gives such an algebra structure by `RingHom.toAlgebra`.
- Flatness of that homomorphism: `hflat : RingHom.Flat (algebraMap R B)`.
- Finite presentation of the algebra: `[Algebra.FinitePresentation R B]`.
  This is not `Module.FinitePresentation R B` or `Module.Finite R B`.
- Every prime of `R`: `p : Spec (.of R)`, whose carrier is `PrimeSpectrum R`.
- Its residue field: `(Spec (.of R)).residueField p`, precisely the dependency's
  recorded quotient of the local stalk by its maximal ideal.
- Every field extension of that residue field: `(K : Type (max u v w)) [Field K]`
  and `ι : (Spec (.of R)).residueField p →+* K`. A unital homomorphism of fields is
  injective, so this specifies exactly an arbitrary field extension. It imposes no
  algebraicity, finite degree, separability or algebraic-closure condition.
- The tensor is over the induced map `R → κ(p) → K`: `[Algebra R K]` and the premise
  `algebraMap R K = ι.comp (((Scheme.ΓSpecIso (.of R)).inv ≫
  (Spec (.of R)).Γevaluation p).hom)` specify exactly that compatibility.
  `ΓSpecIso.inv` sends `R` to its global sections; `Γevaluation` then takes the residue
  at `p`. For any extension `ι`, the composite ring map gives this `Algebra R K`
  via `toAlgebra`. Thus this equality is a description of the tensor's structure,
  not an additional mathematical restriction on the extension. It also avoids a
  file-local instance, a second residue-field definition, or a `let` in the statement.
- The extended fibre is an integral domain: `IsDomain (B ⊗[R] K)`. The tensor is
  Mathlib's module tensor equipped with its canonical commutative-algebra ring structure.
  `IsDomain` includes nontriviality, so the zero fibre is excluded as required.
- The conclusion is projectivity as an `R`-module: `Module.Projective R B`.
  Mathlib's recorded definition already says that the canonical surjection
  `(B →₀ R) →ₗ[R] B` has an `R`-linear section, exhibiting `B` as a direct summand
  of a free module. `Module.Projective.iff_split` gives the equivalent arbitrary-free-module
  formulation. No conclusion clause is lost by stating the projectivity predicate once.

The universe of test fields is `max u v w`, not an independent possibly smaller universe.
The fresh `w` permits arbitrarily large ambient universes; both rings and their residue
fields fit in it by lifting. In particular the identity residue-field extension has a
representative there, so the condition cannot become vacuous through a size mismatch.
No equality between ring universes is imposed.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and
  `RingHom.flat_algebraMap_iff`; the definition is module flatness via `toAlgebra`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`, finite
  polynomial generators with finitely generated kernel.
- `Mathlib.AlgebraicGeometry.ResidueField`: `AlgebraicGeometry.Scheme.residueField`,
  `Scheme.Γevaluation`, and the canonical comparison `Scheme.Spec.residueFieldIso`
  with `Ideal.ResidueField`. `Scheme.Spec.algebraMap_residueFieldIso_inv` confirms
  that the displayed global evaluation map is the usual map to the prime's residue field.
- `Mathlib.Algebra.Module.Projective`: `Module.Projective`, `Module.projective_def'`,
  and `Module.Projective.iff_split`; their definitions and full signatures were read.
- `Mathlib.LinearAlgebra.TensorProduct.Defs` / `.Basic`: `TensorProduct`,
  `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`;
  `Mathlib.RingTheory.TensorProduct.Basic` provides the tensor ring structure.
  The node `def-weil-pbc-module-tensor-product` is a Mathlib leaf; its
  `mathlib_match` is used directly without creating an unnecessary `lean` repair.
- For the retained proof bridges, `Mathlib.AlgebraicGeometry.Pullbacks`:
  `AlgebraicGeometry.pullbackSpecIso` and its projection identities;
  `Mathlib.AlgebraicGeometry.Properties`: the instance `IsIntegral (Spec R)` for a
  domain and `affine_isIntegral_iff` (also reached by `.FunctionField`);
  `Mathlib.AlgebraicGeometry.Geometrically.Integral`:
  `AlgebraicGeometry.GeometricallyIntegral`, whose definition and
  `geometrically_iff_of_commRing` give the all-field-extension scheme criterion.

Edge cases checked against the node and the signature:

- `R = 0`: there are no primes and the fibre condition is vacuous, but a unital
  `R`-algebra is itself zero and hence is a projective zero module. No nontriviality
  binder incorrectly excludes this case.
- `B = 0` over a nonzero ring: a prime and its (lifted) residue field give a zero
  tensor, which is not a domain; the fibre hypothesis correctly fails.
- `B = R[x]`: for any residue-field extension its tensor is `K[x]`, a domain.
  The conclusion is the free, generally infinitely generated, `R`-module. This checks
  that finite presentation was not silently replaced by module finite presentation.
- `R = ℤ`, `B = ℤ[1/2]`: the fibre at 2 is zero, so the hypothesis excludes this
  familiar flat finitely presented algebra which is not projective over `ℤ`.
- `R = k`, `B = k[x,y]/(xy)`: the fibre has zero divisors, so it is excluded.
- Inseparable and transcendental extensions are included: `ι` is an arbitrary field
  homomorphism. A nonreduced base is allowed, for example `R[x]` over
  `R = k[ε]/(ε²)`, since only the fibres are required to be domains.
- The identity extension is included through a lift of the residue field; arbitrary
  `R`-algebra structures on `K` not induced by `p,ι` are intentionally outside the
  tensor condition, precisely because the node means the induced structure.

Searches repeated for this repair (the supplied `msearch.py` wrapper):

- LeanFinder, “flat finitely presented commutative algebra whose every fibre remains
  a domain after every field extension is projective as a module over the base”:
  eight hits, including `Module.Flat.projective_of_finitePresentation`, smoothness/
  flatness and formally-unramified restriction-of-scalars lemmas. No exact match.
- LeanSearch, “flat finitely presented algebra geometrically integral fibres projective
  base module”: eight hits, chiefly module finite-presentation/projectivity equivalences,
  `RingHom.Flat` and `RingHom.FinitePresentation`. No exact match.
- Loogle, `Module.Projective, Algebra.FinitePresentation`: one hit,
  `Algebra.instFiniteH1CotangentOfFinitePresentationOfProjectiveKaehlerDifferential`;
  it concerns the cotangent module, not projectivity of the algebra over the base.
- Mathlib grep, `geometrically.?integral|fibres.*projective|fibers.*projective`:
  12 hits in affine-space geometric integrality and the geometric-integrality class;
  no projectivity theorem of the required kind.
- Direct `rg` in upstream `WeilConjectures` and this project's `lean/Sheaf` for
  geometric-integrality/projectivity combinations found curve, Hilbert and Jacobian
  declarations, none this affine algebra statement. Direct grep of the item id
  in upstream `WeilConjectures` found no declaration. The proposed declaration name
  was also searched in Mathlib, upstream, `lean/Sheaf` and `dag/lean_names_upstream.json`;
  no collision was found.
- The existing DAG duplicate `lem-trf-local-fibres-integral-projective` was read;
  it still has no Lean declaration, so it cannot supply an `existing: true` binding.

No statement correction, new node, dependency redefinition, or statement dispute is needed.
The first `scompile.py` run compiled both the sandbox and the library-path version cleanly
under the prescribed 60-second per-file limit (4.8 s and 7.4 s), without errors or warnings.

## Second reading by Q39

This is the dispatcher's direct-worker workflow: no second agent was started, and the
maintainer's independent review remains the independent review. The following is a
substantive second pass by the writer, with the current node and completed module open.

I re-read the node's exact statement against the signature. The two ring binders are
commutative and permit different universes. `Algebra R B` is the specified ring map,
`RingHom.Flat (algebraMap R B)` is flatness of that same map, and
`Algebra.FinitePresentation R B` is finite presentation as an algebra. None of these
has been changed to a finite-module or Noetherian condition.

For the all-prime clause I checked that `p : Spec (.of R)` really is a prime of `R`.
For the field-extension clause I checked the domain of `ι` is the dependency's actual
scheme residue field, not an arbitrary chosen field. Its canonical `R` map is exactly
`ΓSpecIso.inv` followed by residue evaluation, as checked against
`Spec.algebraMap_residueFieldIso_inv`. The compatibility equation fixes the `R` action
on `K` for the tensor; every extension supplies such an action, so the inner premise
neither discards an extension nor permits an unrelated fibre. `K` has a universe at
least as large as `R` and `B`, so the identity-extension test is available.
`IsDomain` includes the nonzero condition and all-field-extension quantification
has no separability or finiteness restriction.

For the conclusion I opened `Module.Projective`: its field `out` supplies an actual
section of the free-module surjection on the set `B`. Thus projectivity includes the
node's direct-summand formulation. I also read `Projective.iff_split` to check that
no finite-rank qualification was introduced. Zero base and infinite-rank polynomial
algebra examples agree with both the node and Lean.

Finally I re-read the three proof steps against the theorem docstring and imports.
Step 1 retains the tensor comparison, affine fibre-product identification, integrality
of `Spec` of a domain, and geometric-integrality definition. Step 2 retains the existing
Tag 05FT node as the proof dependency; step 3 retains the projective/direct-summand
characterization. No bridge or proof dependency was removed. The missing-stage-2
fault was repaired by adding the actual module and complete `lean` record; the former
non-reading was replaced by this explicit clause audit. This pass found no further
statement mismatch and made no source/DAG statement change.
