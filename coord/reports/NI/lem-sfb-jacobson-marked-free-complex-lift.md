## Worker report

The new module `Sheaf.RingTheory.JacobsonMarkedFreeComplexLift` states
`DerivedCategory.exists_marked_finiteFree_lift_of_jacobson`. Its sole proof is `sorry`.
The DAG statement, dependencies, proof, and all other existing fields are unchanged;
only `lean` is attached. No new definitions or dependency modules are required.

Source read: `literature/stacks-project/more-algebra.tex`, labels
`lemma-lift-complex` (Tag 0BCA, lines 19390–19466) and
`lemma-lift-complex-stably-frees` (Tag 0BCB, lines 19517–19547). The first proof chooses
delta, takes its actual cone, lifts the inclusion, and takes the shifted cokernel.
The node retains the chosen derived inverse marking in this construction. Its eight
proof steps, including the boundary sign and the cutoff argument by finite Nakayama,
are all carried in the theorem docstring. No source-based correction is needed.

Hypothesis and conclusion correspondence:

- Commutative unital ring: `{R : Type u} [CommRing R]`.
- Ideal and one-plus-ideal units: `(I : Ideal R)` and
  `hunits : ∀ x : I, IsUnit (1 + (x : R))`. The subtype quantifier is exactly over I.
- The two derived categories and localizations: independent
  `[HasDerivedCategory.{w} (ModuleCat.{max u v} R)]` and the analogous `{w'}`
  binder over `R ⧸ I`, with the recorded `DerivedCategory.Q` throughout.
- Derived extension of scalars is presented by `L`, its cochain counit `ε`, and
  `[L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso ... (.up ℤ))]`.
  This is exactly the universal-pair property in the recorded change-of-rings
  interface, with ordinary scalar extension fixed to
  `ModuleCat.extendScalars (Ideal.Quotient.mk I)`. The counit is therefore canonical,
  not an unconstrained comparison. This presentation accommodates arbitrary module
  and localization universes without imposing an equality on them. The published
  `ModuleCat.ordinaryDerivedChangeOfRings` and its `.universal` field instantiate
  these binders in the common-universe convention. The generic site version has the
  same `.universal` field in `SheafOfModules.DerivedChangeOfRingsCochainModel`.
  Universal pairs are uniquely isomorphic compatibly with their counits, so this is
  the node's fixed derived extension expressed invariantly, not an extra restriction
  on R, I, K, or F. No arbitrary map replaces a canonical construction.
- Pseudo-coherent object: `K : DerivedCategory ...` and `hK : IsPseudoCoherent K`,
  the dependency's existing bounded-above finite-free-model predicate.
- Given complex F: `CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ`.
  Its terms are finite free precisely by
  `∀ i : ℤ, Module.Free (R ⧸ I) (F.X i) ∧ Module.Finite (R ⧸ I) (F.X i)`.
- Given integer and cutoff: `(b : ℤ)` and `hFbound : F.IsStrictlyLE b`.
  Mathlib's `CochainComplex.isStrictlyLE_iff` identifies this with
  `∀ i, b < i → IsZero (F.X i)`: the cutoff is literal termwise vanishing.
- Every specified marking is the binder `α : L.obj K ≅ Q.obj F`.
- Lifted complex, derived identification, and chain-level identification are the
  dependent existential binders `P`, `β : Q.obj P ≅ K`, and
  `θ : ((ModuleCat.extendScalars ...).mapHomologicalComplex (.up ℤ)).obj P ≅ F`.
  This is an isomorphism of actual complexes, including all differentials.
- The first two conjuncts give `P.IsStrictlyLE b` with exactly the same b and
  `∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)`.
- The final conjunct is
  `ε.app P ≫ Q.map θ.hom = L.map β.hom ≫ α.hom`.
  Lean composition is diagrammatic: this is precisely
  Q(theta) composed with c_P equals alpha composed with L(beta).
  The component `ε.app P` is c_P: the canonical universal counit evaluated on
  the bounded-above free, hence K-flat, complex P. Its invertibility follows from
  the K-flat computation clause of the same derived-change-of-rings theorem;
  an extra comparison or a replacement marking is not chosen.
- There is no nilpotence, completeness, nonzero-ring, or nonnegative-cutoff binder.

Statement dependency declarations read and used:

1. `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
   `HasDerivedCategory`, `DerivedCategory.Q`, with their complete signatures and
   localization docstrings.
2. `WeilConjectures.RingTheory.RingPseudoCoherent`:
   `DerivedCategory.IsPseudoCoherent`, with its actual existential definition.
3. `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
   `ModuleCat.OrdinaryDerivedChangeOfRings` (especially `.counit`, `.universal`,
   `.computes`), `ModuleCat.ordinaryDerivedChangeOfRings` and
   `ModuleCat.ordinaryDerivedExtendScalars`; its publicly retained
   `SheafOfModules.DerivedChangeOfRingsCochainModel` has the corresponding generic
   cochain universal-pair presentation. The theorem uses the existing Mathlib
   `Functor.IsLeftDerivedFunctor` of exactly these universal fields, rather than
   creating a second definition of derived scalar extension.

Every already stated proof dependency is imported without `public`, using its
recorded upstream or Mathlib module: projectivity, finite Nakayama, flatness,
bounded-flat K-flatness, projective derived-map representatives, cone properties,
acyclic lift, strict lift, cone cokernel, reduced splitting, projective freeness
from free reduction, canonical SES triangles, Hom exactness, and degreewise split
triangles. `lem-sfb-ringed-kflat-pullback-ses-triangle` has neither a Lean record nor
a Mathlib match at inspection time, so there is no proof-only module to import;
its proof step is documented. It is not needed to type this statement.

Edge cases checked mathematically before writing:

- I = 0: reduction is the identity up to its canonical universal comparison;
  the prescribed alpha is retained by choosing the derived identification accordingly.
- F = 0: the asserted lift vanishes above the requested b, and the Jacobson/Nakayama
  argument detects zero terms. No nonempty basis is assumed.
- The zero ring is permitted. I = top in a nonzero ring fails the stated unit
  hypothesis at x = -1, as it should; no proper-ideal hypothesis is added.
- R = Z localized at (p), I = (p): the ideal is not nilpotent but satisfies the
  one-plus-ideal unit condition, and the statement still applies.
- Negative b and complexes unbounded below are allowed. The cutoff is termwise,
  not merely a bound on cohomology.
- Nontrivial derived automorphisms of the model cannot be forgotten: alpha is a
  specified binder and appears in the final equality.
- `max u v` allows modules larger than the ring; w and w' are independent.

Searches actually run using the prescribed msearch wrapper:

- LeanFinder: “Lift a prescribed bounded above finite free complex and its derived
  isomorphism modulo a Jacobson ideal”. Eight hits, all adic-completion lifting
  statements (`IsAdicComplete.mkQ_comp_lift`, `AdicCompletion.eval_lift`, etc.),
  none the required complex statement.
- Loogle: `CochainComplex, Module.Free`. Zero hits.
- Mathlib grep: `lift.*[Cc]omplex|[Cc]omplex.*lift|[Pp]seudo[Cc]oherent` in
  `RingTheory`. Two hits in `Etale/Kaehler.lean` concern cotangent base change,
  not this statement.
- LeanSearch: “A pseudo coherent derived object lifts a prescribed finite free
  complex modulo a Jacobson radical ideal with compatible isomorphism”. Eight
  hits on adic lifts, formal smoothness, and localization functors, none exact.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id, marked lifting,
  complex lifting and `ordinaryDerivedExtendScalars`: no exact existing statement.
  The closest existing statement is
  `DerivedCategory.exists_marked_finiteFree_lift_of_nilpotent` in
  `Sheaf.RingTheory.NilpotentMarkedFreeComplexLift`; its nilpotence assumption
  excludes the general Jacobson case. The upstream `StablyFreeComplexLift`
  theorem is unmarked. Neither may be recorded as an exact existing match.
  `dag/lean_names_upstream.json` was also searched by item id and free-complex names.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by NI

Single-worker rereading: the dispatcher explicitly forbids starting another agent;
the maintainer supplies the independent delivery review. I reopened the node and
module and compared every binder and conjunct as listed above. The changes are
only its new Lean record. In particular, the nonnilpotent Jacobson case, the exact
integer b, the direction of beta, the chain-level nature of theta, and the
appearance of the specified alpha are preserved. The counit's direction matches
c_P, so the displayed equality has the same source and target as the node's.
The universal-property binder prevents an arbitrary comparison from satisfying
the interface. No mismatch or statement correction was found on rereading.

## Validation

The prescribed scompile.py passed both the sandbox check and compilation under
the actual library module name. No errors or unexpected warnings remain. The initial
probe caught scalar-extension universe inference selecting only u; explicitly writing
`ModuleCat.extendScalars.{u, u, max u v}` repaired it without reducing generality.
The node record signature was regenerated verbatim from the final Lean header.
The required delivery dry run is run after this report is written.
