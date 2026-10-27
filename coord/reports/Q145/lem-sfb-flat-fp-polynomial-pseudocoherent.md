## Worker report

The module `Sheaf.RingTheory.FlatFinitePresentationPolynomialPseudoCoherent` states
`DerivedCategory.isPseudoCoherent_single_polynomialPresentation_of_flat_finitePresentation`.
Its only theorem has proof `sorry`. The item is unchanged outside its `lean` field.
There are no new notions, dependency repairs, statement corrections or disputes.

Hypothesis and conclusion correspondence:

- Commutative rings R and C and their given ring map are `{R : Type uR}`,
  `{C : Type uC}`, `[CommRing R]`, `[CommRing C]`, `[Algebra R C]`, with map
  `algebraMap R C`. An algebra structure is precisely the specified commutative ring map.
- Finite presentation is `[Algebra.FinitePresentation R C]`, algebra finite presentation,
  not module finite presentation.
- Flatness of this very map is `hflat : (algebraMap R C).Flat`.
- The arbitrary integer n >= 0 is `{n : ℕ}`, with no positivity assumption.
- The polynomial ring P is `MvPolynomial (Fin n) R`.
- The specified R-algebra presentation is
  `π : MvPolynomial (Fin n) R →ₐ[R] C`; its surjectivity is
  `hπ : Function.Surjective π`. It is not replaced by a chosen presentation.
- The P-module C is obtained by `ModuleCat.restrictScalars π.toRingHom` applied to the
  regular C-module. `ULift.{max uR v} C` only puts this same regular module in
  `Type (max uR uC v)`; its scalar action satisfies
  `(c • x).down = c * x.down`, and `ULift.moduleEquiv` identifies it with C.
  Thus the resulting P-action is exactly p • c = π(p)c.
- `singleFunctor (ModuleCat.{max uR uC v} (MvPolynomial (Fin n) R)) 0` places that
  module in degree zero in D(P). The explicit `HasDerivedCategory.{w}` binder chooses
  the localization universe, as in the recorded abstract-derived-category dependency.
- `DerivedCategory.IsPseudoCoherent` is the dependency's definition, whose body is
  existence of a complex E, a bound b, `E.IsStrictlyLE b`, finite free terms in
  every integer degree, and `Nonempty (Q.obj E ≅ C[0])`. This also renders the node's
  equivalent bounded-above finite-free formulation, without adding a second conjunct.
- There is no `IsNoetherianRing R` or `IsNoetherianRing C` binder, and no finiteness
  or flatness assumption on π or its kernel beyond the actual node hypotheses.

Recorded dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, defined using `Module.Flat`;
  `RingHom.flat_algebraMap_iff` identifies the algebraMap formulation.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.singleFunctor`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- Mathlib supplies `ModuleCat.restrictScalars`, `ModuleCat.of`, and
  `ULift.moduleEquiv`; no duplicate module or polynomial notion is defined.

All available proof-dependency modules are imported without `public`:
`WeilConjectures.RingTheory.FlatFinitePresentationModel` (the model theorem),
`Mathlib.RingTheory.FiniteType` (Noetherian finite-type algebras),
`WeilConjectures.RingTheory.FiniteFreeResolution` (finite free resolutions),
`WeilConjectures.Mathlib.RingTheory.Flat.Equalizer` (flat syzygies),
`Mathlib.RingTheory.Flat.Equalizer` (tensor injectivity), and
`Sheaf.RingTheory.PolynomialPresentationPseudoCoherence` (presentation independence).
The remaining proof dependencies are also statement dependencies, publicly imported.
The theorem docstring gives all five steps of the node's proof with their dependencies.

Sources checked: the local Stacks `more-algebra.tex`,
`lemma-flat-finite-presentation-perfect` (067J), and
`lemma-relatively-pseudo-coherent` (065H), including their proofs. The former descends
flatness to a Noetherian model, not to R; the latter covers every finite presentation.
The latest blueprint's direct-image stability statement was also read; this is a
supporting algebra lemma, not that unit's statement.

Edge cases checked mathematically: n = 0 (the presentation is R → C), arbitrary
characteristic, zero rings, zero module and zero free ranks. Zero variables require no
`Nonempty (Fin n)`. The zero ring is not excluded by `Nontrivial`. Non-Noetherian R
and C are allowed. The representing complex need not be bounded below. The independent
universes uR and uC are retained, and the module universe contains both rings; v permits
arbitrarily larger module universes. `ULift` excludes no regular module.

Searches performed using the prescribed `msearch.py`:

- LeanFinder: "A flat finitely presented algebra is pseudo coherent over every finite
  polynomial ring presenting it". Eight hits, chiefly `Algebra.Smooth.flat`,
  `Algebra.Smooth.finitePresentation`, and `Algebra.FinitePresentation`; none gives
  this pseudo-coherence conclusion for arbitrary flat finitely presented algebras.
- LeanSearch: "A flat finitely presented algebra admits a bounded above finite free
  resolution over a polynomial presentation". Eight hits, including
  `RingHom.FinitePresentation`, `Module.Flat.projective_of_finitePresentation`,
  `AlgHom.FinitePresentation`, and `Algebra.Presentation.exists_presentation_fin`.
  Module finite presentation is a different hypothesis; none is an exact match.
- Loogle: `"IsPseudoCoherent"`; zero hits.
- Mathlib grep: `pseudo.?coher|pseudoCoherent`, subdirectory `RingTheory`; zero hits.
- Direct rg with `flat.*[Pp]seudo|[Pp]seudo.*flat` over both `lean/WeilConjectures`
  and `lean/Sheaf` found scheme-level flat pseudo-coherence, derived Hom base-change,
  and consumers of this item, but no theorem with this statement. In particular the
  affine finite-presentation flat theorem is about complexes on schemes.
- The exact item id was searched in both source roots: no existing declaration.
  The proposed declaration and module names were searched in both roots and
  `dag/lean_names_upstream.json`: no collision.

Validation: `scompile.py Q145 lem-sfb-flat-fp-polynomial-pseudocoherent` compiled the
single delivered module both as sandbox source and under its final module name on the
server (5.7 s and 9.4 s). No errors or unexpected warnings. All variables and universes
are explicitly bound; `set_option autoImplicit false` enforces this.

## Second reading by Q145

Final separate reading by the same dispatcher worker; no additional agent was started.
The independent review is the maintainer's delivery review, as specified in this brief.
I reopened the node and the completed signature: the ring map is the same algebraMap
used by π's R-algebra structure; finite presentation and flatness concern R → C;
π is arbitrary and surjective; n may be zero. Restriction precedes the single functor,
so the degree-zero object is in D(P) and its action is via π. Unfolding the existing
pseudo-coherence definition gives exactly the stated finite-free characterization.
The universe lift transports the regular module and adds no mathematical hypothesis.
No statement mismatch or correction was found. The proof remains only `sorry`.
