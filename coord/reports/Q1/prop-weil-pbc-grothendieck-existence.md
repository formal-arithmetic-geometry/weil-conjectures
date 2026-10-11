## Worker report

Wrote `lean/Sheaf/AlgebraicGeometry/GrothendieckExistence.lean`, declaring
`AlgebraicGeometry.grothendieck_existence`. The sole proof is `by sorry`; no definition,
instance, axiom, new node, dependency replacement or statement correction is introduced.
The JSON copy changes only `lean`. The signature is copied verbatim, including newlines.

Source read: [Stacks 088E](https://stacks.math.columbia.edu/tag/088E) and
[Stacks 088F](https://stacks.math.columbia.edu/tag/088F). This machine does not hold
`literature/stacks-project/coherent.tex`; the source was read at the official tag pages.
The node's ten proof steps are carried into the theorem docstring for stage 3.

Clause-by-clause correspondence:

* A is a commutative Noetherian ring: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
* The ideal and completeness are `(I : Ideal A) [IsAdicComplete I A]`. Completeness includes
  separatedness for the adic topology; no separate nonzero/proper-ideal restriction is added.
* S is `Spec (.of A)`; the structure morphism is `(f : X ⟶ Spec (.of A))`.
* Separated and finite type mean `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`;
  neither properness of X nor projectivity is assumed.
* S_n is literally `Spec (.of (A ⧸ I ^ (n + 1)))`. Its map to S is
  `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))`.
* X_n is the actual `pullback f` along that map. The two projections are `pullback.fst`
  (j_n) and `pullback.snd` (X_n → S_n). This uses the representation prescribed by the
  dependency `def-pc-base-change`'s `lean.note`, rather than a separate base-change notion.
* The binder `i` has source X_n and target X_(n+1). `hi` fixes its first projection to j_n.
  `hp` fixes its second projection to the base transition followed after `pullback.snd`.
  The base transition is Spec of `Ideal.Quotient.factor`, with the ideal containment
  `Ideal.pow_le_pow_right (Nat.le_succ (n + 1))`. These two equations uniquely specify the
  canonical transition map by the pullback universal property. They are specifications
  of the named object in the node, not an additional condition on A, I or f. Both j_n and
  i_n are closed immersions because these are base changes of surjective quotient maps.
* Restriction of a module/morphism is `.obj`/`.map` of
  `Scheme.Modules.tensorPullback (pullback.fst ...)`, exactly j_n^*, not Mathlib's different
  `Scheme.Modules.pullback`.
* `c n` is a natural isomorphism from j_(n+1)^* followed by i_n^* to j_n^*. `hc` fixes it to
  the inverse of the dependency's chosen composition isomorphism, followed by `eqToIso`
  from `hi`. Thus c is specified comparison data, not a freely chosen family of module
  isomorphisms. The dependency exposes composition comparison by `Nonempty`; this
  statement uses `Classical.choice` of that very declaration and no new comparison notion.
* Part (a) quantifies over F,G in X.Modules. Each has its own
  `RingedSpace.IsCoherent X.toRingedSpace` and `Scheme.Modules.HasSupportProperOver f`
  hypothesis. The family `v` consists of linear sheaf morphisms on every X_n. Its equation
  is `(c n).hom.app G ≫ v n = (tensorPullback (i n)).map (v (n+1)) ≫ (c n).hom.app F`.
  This is the node's compatibility equation in Lean's left-to-right composition order.
  `∃! w : G ⟶ F, ∀ n, j_n^*.map w = v n` expresses bijectivity of precisely the
  restriction map onto the compatible families (unique preimage for every family).
  Naturality of c ensures every restricted morphism is compatible.
* Part (b) quantifies over F_n on the actual X_n and the isomorphisms
  `φ n : (tensorPullback (i n)).obj (F (n+1)) ≅ F n`. It assumes coherence for every n.
  Proper support of F_0 is measured over S_0 using `HasSupportProperOver (pullback.snd ...)`;
  local finite type of this projection follows by base change from f, without a new binder.
* Its conclusion supplies G on X, coherence, support proper over S, and an indexed family
  `ψ n : j_n^* G ≅ F n`. The concluding equality is
  `i_n^*.map (ψ (n+1)).hom ≫ (φ n).hom = (c n).hom.app G ≫ (ψ n).hom`, precisely the
  required compatibility after reversing composition notation. The conjunction joins
  the whole of (a) and the whole of (b) into one theorem.

Dependency declarations read and used:

* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness reading.
* `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete I A`.
* `Mathlib.AlgebraicGeometry.Morphisms.Proper` / `Separated`: `IsSeparated`;
  properness inside the recorded support predicate is `IsProper`.
* `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; together with
  `QuasiCompact` it renders finite type.
* `Sheaf.AlgebraicGeometry.BaseChangeConventions`: its documented base-change encoding is
  `Limits.pullback` with `pullback.fst` and `pullback.snd`, used directly here.
* `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` and
  `Scheme.Modules.nonempty_tensorPullbackComp`, including their signatures and docstrings.
* `Sheaf.AlgebraicGeometry.Coherent`: `RingedSpace.IsCoherent`, on the identical carrier
  X.Modules, not a private coherence predicate.
* `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `Scheme.Modules.HasSupportProperOver`, with the nonzero-stalk locus and reduced structure.
* `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`; the node's
  specified immersions are already forced quotient base changes, not extra hypotheses.

Edge cases checked before writing: n = 0 gives A/I, and the transition goes from quotient
by I^1 to quotient by I^2 on spectra; direction of Spec and tensor pullback is correct.
I = 0 gives the constant tower (the comparisons need not be definitional identities).
I = top forces the complete ring to be zero; the spectra and modules are empty/zero.
Empty X, zero modules and systems, nilpotent I, and arbitrary characteristic are all allowed.
Only the schemes' and ring's shared universe u is used; the index is ℕ, with no undersized
universe of test objects. The module universe agrees with the recorded coherence predicate.
No false-statement or missing-notion fault was found.

Searches (all remote-service searches made by the prescribed msearch.py):

* LeanSearch: `Grothendieck existence theorem compatible coherent modules on adic thickenings
  with proper support` — service returned Internal Server Error; recorded unavailable.
* LeanFinder: `Grothendieck existence theorem fully faithful algebraization coherent sheaves
  formal thickenings` — eight results about forgetful fully faithful functors for sheaves,
  étale schemes and ideal-sheaf subschemes, none about completion or algebraization.
* Loogle: `IsAdicComplete, IsNoetherianRing` — only
  `AdicCompletion.instIsAdicCompleteMaximalIdeal`, a local-ring completion instance,
  not this statement.
* Mathlib grep: `grothendieck.existence|formal.completion|adicThickening` in
  AlgebraicGeometry — zero hits.
* rg of `grothendieck_existence|GrothendieckExistence|grothendieck.existence|formal.completion`
  over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json — no hits.
* grep for the exact node id in WeilConjectures — no hits.
* Additional rg for adic/formal thickenings and transition comparisons in the project's
  AlgebraicGeometry sources found first-order/dual-number notions, not this theorem.

Validation: scompile.py compiled the 107-line module cleanly on the server in 2.5 seconds.
The delivery dry run is the final gate; the independent second reading is deliberately
left for the second worker.

## Second reading by Q1

Independently read the repository node, the delivered theorem and all nine statement
 dependency nodes and their recorded declarations. No statement correction, new node or
 dependency module is present. Read the actual Stacks `coherent.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/coherent.tex at
`theorem-grothendieck-existence` and `remark-reformulate-existence-theorem`; the local
literature directory is absent. Also checked official Tags 088E and 088F. Their hypotheses
are precisely completeness of the Noetherian commutative base and separated finite type X;
properness of X is only a special case, not an assumption. The source indices start at 1;
the node and Lean shift them to start at 0.

Object, hypothesis and conclusion checklist (all verdicts pass):

1. Noetherian commutative A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
   Opened Noetherian/Defs: the predicate is Noetherian as an A-module, equivalently every
   ideal finitely generated. No domain, nontriviality or field hypothesis appears.
2. Ideal I and I-adic completeness: `(I : Ideal A) [IsAdicComplete I A]`.
   Opened AdicCompletion/Basic: completeness includes `IsHausdorff`, and
   `AdicCompletion.of_bijective_iff` identifies it with the node's bijective canonical map.
3. S and its thickenings: `Spec (.of A)` and
   `Spec (.of (A ⧸ I ^ (n + 1)))`, the latter occurring as the domain of Spec.map of
   `Ideal.Quotient.mk`. These are the same quotient rings, without additional choices.
4. X over S, separated and finite type: `{X : Scheme.{u}} (f : X ⟶ Spec (.of A))`
   with `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
   The dependency definitions use exactly the diagonal criterion and the conjunction
   defining finite type. No separate Noetherian-X or proper-f instance is assumed.
5. X_n: `pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ...)))`.
   Opened BaseChangeConventions: its module documentation explicitly prescribes this
   representation and its fst/snd projections, rather than its moduleBaseChange functor
   for the scheme itself. Here fst is j_n and snd is the structure map to S_n.
6. Transition i_n and j_n: `i n` with the displayed domain and codomain, `hi n`
   fixing its first projection and `hp n` fixing its second projection. The latter uses
   Spec.map of the quotient factor A/I^(n+2) -> A/I^(n+1). Pullback uniqueness forces
   the canonical i_n; the equations introduce no extra geometric hypothesis. j_n and
   i_n are closed immersions as base changes of these quotient immersions, so there is
   no need to assume their closed-immersion instances separately.
7. Module restriction and comparison: every j_n^* is the dependency's
   `Scheme.Modules.tensorPullback (pullback.fst ...)`. Opened TensorPullback: its object
   is the inverse-image module followed by change of rings, not the sectionwise functor
   called pullback in Mathlib. `c n` is a natural isomorphism with source j_(n+1)^* then
   i_n^* and target j_n^*. `hc n` chooses the dependency's composition isomorphism,
   inverts it and transports along hi. This is a fixed shared comparison convention;
   c is not arbitrary unrelated module-by-module data. The theorem needs only these
   consecutive comparisons, not additional coherence data for a general diagram.
8. Part (a), objects and hypotheses: `∀ (F G : X.Modules)` followed by coherence of
   each and `HasSupportProperOver f` of each. Opened Coherent: finite type plus finite
   type kernels of every map from finite free modules on every open. Opened
   ClosedSubsetProperOverBase: the support is precisely the nonzero-stalk locus,
   closedness is existentially witnessed by a Closeds, and properness is of the reduced
   induced closed subscheme. These are the dependency notions, with no private copies.
9. Part (a), compatible families: `v n : j_n^* G ⟶ j_n^* F` for every natural n,
   with `(c n).hom.app G ≫ v n = (tensorPullback (i n)).map (v (n+1)) ≫
   (c n).hom.app F`. Reversing Lean's composition notation gives exactly the node's
   u_n composed with c_n equals c_n composed with i_n^*u_(n+1).
10. Part (a), bijection: `∃! w : G ⟶ F, ∀ n, j_n^*.map w = v n` is unique
    preimage for each compatible family. Naturality of c supplies compatibility of
    the image of every w, so this states the specified restriction map's bijectivity.
11. Part (b), system: `∀ (F : ∀ n, X_n.Modules) (φ : ∀ n,
    (tensorPullback (i n)).obj (F (n+1)) ≅ F n)` followed by coherence for every n.
    No separate higher transition maps or extra cocycle condition are introduced.
12. Part (b), proper support: `HasSupportProperOver (pullback.snd ... I^(0+1))
    (F 0)`. The base is S_0, not S or X; its locally-finite-type instance is supplied
    by base change of f. Only this first term needs the support hypothesis.
13. Part (b), algebraization: `∃ G : X.Modules`, coherence and support proper over S,
    and `∃ ψ : ∀ n, j_n^* G ≅ F n`. The equation
    `i_n^*.map (ψ (n+1)).hom ≫ (φ n).hom = (c n).hom.app G ≫ (ψ n).hom`
    is precisely φ_n composed with i_n^*ψ_(n+1) equals ψ_n composed with c_n.
    The outer conjunction states both (a) and (b), with the prescribed quantifier order.

Edge cases: the index is always all natural numbers, so an empty index is not an object
of this node. n=0 uses A/I and the next term A/I^2 with the correct contravariant Spec
and pullback directions. I=0 gives the constant tower; no identity-comparison assumption
is added. I=top is allowed (completeness forces A to be the zero ring). Empty X and zero
modules/systems are allowed, as are nilpotent ideals and every characteristic. Universe u
is explicitly bound, covers rings and schemes of arbitrary size by universe lifting,
and matches the recorded module/coherence universe. There is no undersized test category
or unrelated index universe. Checked all variables and the 100-character line bound.

Independent searches, using different wording from the worker:

* LeanFinder via msearch.py: `algebraize compatible coherent sheaves infinitesimal
  neighborhoods complete ring proper support`. Eight hits: affine-transition-limit
  section lemmas, spreading-out and formally-unramified lemmas, and ideal-sheaf glue
  data. Their displayed signatures concern sections or scheme maps, not coherent
  algebraization or the equivalence here. No match.
* Loogle via msearch.py: `IsAdicComplete, Scheme` returned unknown identifier Scheme;
  this query is unusable, not evidence of absence.
* LeanSearch via msearch.py: `Existence equivalence coherent modules compatible
  infinitesimal restrictions complete noetherian base`. Internal Server Error; recorded
  unavailable, without claiming a no-match verdict.
* rg over Mathlib/AlgebraicGeometry, WeilConjectures and repository lean/Sheaf for
  `algebraiz|algebrais|grothendieck.?existence|formal.?completion|formal.?sheaf`.
  Inspected the project hits in CoherentFormalModule: they define formal modules,
  completion and its proper-support restriction, but do not state this equivalence,
  compatible-family full faithfulness or algebraization. Other upstream/Mathlib hits
  are the algebraize tactic and elementary affine limit statements. No duplicate.

Mismatches and repairs: no mathematical or signature mismatch found. The proof docstring
omitted the node's derivation that X is Noetherian and its empty-X induction case. Added
`pqf-lem-locnoeth-lft` to step 1 and the zero-system algebraization on the empty scheme to
step 4. Retained the ten-step proof route and all correct Lean. No statement, dependency
or node field changed. Signature equality with lean.statement checked programmatically;
only the docstring changes. There is one named theorem with `by sorry` and no definition,
instance, private notation, hollow data or proved auxiliary result.
