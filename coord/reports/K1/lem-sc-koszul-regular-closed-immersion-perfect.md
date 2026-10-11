## Worker report

Module: `Sheaf.AlgebraicGeometry.KoszulRegularClosedImmersionPerfect`.
Declaration: `AlgebraicGeometry.koszulRegular_closedImmersion_perfect`.
It states the local sheafified Koszul resolution, boundedness and finite freeness
of the Koszul terms, perfectness of the closed immersion, and perfectness of the
pushed-forward structure sheaf in the shared derived category. Its only proof is
`sorry`; it introduces no definitions or auxiliary nodes.

Source checked: https://stacks.math.columbia.edu/tag/068C, Lemma 37.61.7.
The local Stacks source directory is absent on this machine, so the tag was opened
online. Its proof explicitly identifies the Koszul complex as a finite free
resolution of A/I and assumes no Noetherian condition.

Hypotheses and clauses, in order:

- Schemes Z and Y: `{Z Y : Scheme.{u}}`; the named closed immersion:
  `(i : Z ⟶ Y) [IsClosedImmersion i]`.
- Every point has an affine open neighbourhood: `h` begins
  `∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ ...`.
  The coordinate ring is the canonical `Γ(Y, U)`; every affine open is its
  spectrum via `IsAffineOpen.isoSpec`, so choosing this ring loses no charts.
- The ideal defining the inverse image is `I : Ideal (Γ(Y, U))`, with
  `e : (i ⁻¹ᵁ U).toScheme ≅ Spec (CommRingCat.of (Γ(Y, U) ⧸ I))` and
  `i ∣_ U ≫ U.toSpecΓ = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
  The equation specifies the quotient immersion over U, not merely an abstract
  isomorphism of schemes.
- Finite sequence generating that ideal: `(r : ℕ) (f : Fin r → Γ(Y, U))` and
  `I = Ideal.span (Set.range f)`.
- Koszul-regularity: `RingTheory.Sequence.IsKoszulRegular f`, exactly the
  dependency's vanishing of positive Koszul homology.
- Local quasi-isomorphism on that sequence: the first conjunct quantifies over
  an affine chart and any such quotient presentation and Koszul-regular generators.
  Its `q` maps the degreewise sheafification of
  `ExteriorAlgebra.koszulComplex (Γ(Y, U) : Type u) r f` to the complex concentrated
  in degree zero at `(restrictFunctor U.ι).obj ((pushforward i).obj (unit ...))`.
  `QuasiIso q` is the asserted local quasi-isomorphism. Sheafification is the existing
  `tilde.functor Γ(Y, U)`, followed by restriction along the isomorphism
  `hU.isoSpec.hom : U.toScheme ⟶ Spec Γ(Y, U)`.
- Finite free terms: for every n, the recorded Koszul term satisfies
  `Module.Free (Γ(Y, U) : Type u) ... ∧ Module.Finite (Γ(Y, U) : Type u) ...`.
  These are precisely the modules whose tilde sheaves are the displayed local
  Koszul complex terms. No unrelated resolution is substituted.
- Bounded Koszul complex: `∀ n : ℕ, r < n → IsZero (... .X n)`.
  Negative terms are zero by the existing natural-indexed chain-complex convention.
- Perfect immersion: the second conjunct is `IsPerfectClosedImmersion i`.
- Perfect pushforward: the final conjunct is `Scheme.IsPerfect Y` applied to
  `DerivedCategory.singleFunctor ... 0` of
  `(SheafOfModules.pushforward i.toRingCatSheafHom).obj (SheafOfModules.unit ...)`.
  This is i_* O_Z in degree zero, with the shared SheafOfModules category instance;
  it is not an arbitrary derived object or derived pushforward.
- The two `HasDerivedCategory.{w}` binders supply the localization models required
  by `Scheme.IsPerfect` on Y and its open sites; they impose no geometric condition.
  The local resolution uses the existing Scheme.Modules category, whereas the
  final perfectness uses the mandated shared SheafOfModules derived category.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (the dependency's mathlib_match).
- `Sheaf.RingTheory.KoszulRegularSequence`: `RingTheory.Sequence.IsKoszulRegular`.
- `Sheaf.Paper.KoszulComplex`: `ExteriorAlgebra.koszulComplex` (imported transitively
  by KoszulRegularSequence).
- `Sheaf.AlgebraicGeometry.PerfectClosedImmersion`:
  `AlgebraicGeometry.IsPerfectClosedImmersion`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`.

Supporting existing constructions: `IsAffineOpen.isoSpec`, `tilde.functor`,
`Scheme.Modules.restrictFunctor`, `Scheme.Modules.pushforward`,
`SheafOfModules.pushforward`, `SheafOfModules.unit`, `ChainComplex.single₀`,
`Functor.mapHomologicalComplex`, `QuasiIso`, `DerivedCategory.singleFunctor`.
All geometric notions come from the dependency modules or Mathlib.

Edge cases checked before writing: Y empty makes the neighbourhood hypothesis and
perfectness conditions vacuous; the empty open remains an allowable chart.
Z empty corresponds to I=A and an acyclic Koszul complex for unit generators.
r=0 is allowed, with I=0, degree-zero A and no positive terms.
r=1 gives A → A; regularity is exactly vanishing of its first homology.
The zero coordinate ring is allowed; Module.Free and Module.Finite allow its zero
modules. No characteristic, reducedness, finiteness or Noetherian assumptions are
introduced. Universes u and w are explicitly bound, and no test universe restricts
the class of affine charts. No statement correction or dispute was needed.

Searches for an existing statement:

- msearch.py leanfinder: "A Koszul regular closed immersion is perfect and its
  structure sheaf has a Koszul resolution". Eight hits about smooth loci,
  formal smoothness and cotangent complexes; no match.
- msearch.py loogle: "IsClosedImmersion, Perfect". Zero hits; the service reports
  unknown identifier IsClosedImmersion.
- msearch.py leansearch: "Koszul regular immersion perfect". Unavailable:
  Internal Server Error; no verdict inferred from the unavailable service.
- msearch.py grep: "Koszul|koszul|IsPerfectClosedImmersion". Three Mathlib hits:
  a local-cohomology comment, a Koszul-connection comment, and the regular-sequence
  TODO for Koszul regularity; no theorem.
- rg of pinned Mathlib AlgebraicGeometry and RingTheory for "Koszul|koszul": only
  the regular-sequence TODO. rg of WeilConjectures and lean/Sheaf found the
  project's general Koszul definitions and projective-line Koszul short complex,
  not this theorem. rg for the node id and the new full declaration name in
  WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json had no hits.

Validation: scompile.py on the final module returned exit code 0, compiled in
2.7 seconds, with no errors or warnings. The first two attempts corrected the
bundled coordinate ring passed to tilde.functor and used hU.isoSpec.hom for the
restriction along the affine identification. The node copy changes only `lean`,
whose signature is extracted verbatim from the final module.

## Second reading by K1

I independently opened the item node, its delivered module, all six statement
dependency nodes, and their recorded declaration sources. The list below is my
reading of the node before comparing it with Lean.

1. Objects: schemes Y and Z, and a closed immersion i:Z→Y. Lean has
   `{Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]`. Verdict: exact.
   Mathlib's Scheme extends LocallyRingedSpace with local affine charts;
   IsClosedImmersion requires a closed embedding and surjective stalk maps.
2. Hypothesis: every y in Y has an affine neighbourhood U=Spec A. Lean has
   `∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ ...` in h.
   Verdict: exact. A is `Γ(Y, U)`; `hU.isoSpec` canonically identifies the
   open subscheme with its spectrum, so this loses no affine presentation.
3. Hypothesis: the ideal defining Z over U is generated by a finite sequence.
   Lean introduces `I : Ideal (Γ(Y, U))`, `r : ℕ`, `f : Fin r → Γ(Y, U)`
   and `I = Ideal.span (Set.range f)`. The isomorphism e identifies
   `(i ⁻¹ᵁ U).toScheme` with Spec(A/I), and
   `i ∣_ U ≫ U.toSpecΓ = e.hom ≫ Spec.map ... (Ideal.Quotient.mk I)`
   makes that identification over U. Verdict: exact; an abstract isomorphism
   alone would not suffice, but the required equation is present.
4. Hypothesis: this sequence is Koszul-regular over A. Lean uses
   `RingTheory.Sequence.IsKoszulRegular f`. Verdict: exact. I read its body:
   positive homology of `ExteriorAlgebra.koszulComplex A r f` is zero.
   It adds neither properness of I nor a nonzero quotient condition.
5. Conclusion: locally i_*O_Z is quasi-isomorphic to the Koszul complex on
   that very sequence. Lean's first conjunct universally quantifies a chart
   and its quotient presentation satisfying the preceding conditions, then
   gives `∃ q : ... ⟶ ..., QuasiIso q`. Verdict: exact local resolution.
   This universal conditional spells out the node's resolution on a chosen
   qualifying chart; h supplies such charts at every point. It imposes no
   existence of qualifying generators on other opens. The source complex is
   the recorded Koszul complex mapped degreewise by `tilde.functor Γ(Y, U)`
   and restriction along `hU.isoSpec.hom`. The target is `single₀` of the
   restriction of the actual pushforward of `SheafOfModules.unit Z.ringCatSheaf`.
   I read Modules.pushforward and restrictFunctor: these are direct image
   and open restriction, respectively, not an unrelated sheaf or module.
6. Conclusion: those terms are finite free and the complex is bounded.
   Lean asserts `∀ n : ℕ, Module.Free A (K.X n) ∧ Module.Finite A (K.X n)`
   and `∀ n : ℕ, r < n → IsZero (K.X n)`. Verdict: exact. I read K's
   construction: its terms are exterior powers of `Fin r →₀ A`, and its
   differential is contraction with the linear form defined by f. Negative
   degrees are zero by the recorded natural-indexed complex convention.
7. Conclusion: i is a perfect closed immersion. Lean has
   `IsPerfectClosedImmersion i`. Verdict: exact. Its dependency definition
   asks for the same affine quotient presentation and a bounded finite
   projective resolution of A/I, precisely the node's local criterion.
8. Conclusion: i_*O_Z is perfect on Y. Lean has `Scheme.IsPerfect Y` of
   `DerivedCategory.singleFunctor ... 0` applied to
   `(SheafOfModules.pushforward i.toRingCatSheafHom).obj (SheafOfModules.unit ...)`.
   Verdict: exact object in degree zero. I read IsPerfect, IsStrictlyPerfect,
   schemeDerivedCategory, and moduleRings. They use the shared category of
   all structure-sheaf modules, derived open restriction, and local bounded
   complexes of finite free summands. The two HasDerivedCategory binders
   are the dependency's localization-model parameters, not geometric
   assumptions or smaller test-scheme universes.

Source: the local Stacks .tex tree is absent. I read the upstream .tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
the section `section-perfect` and lemma `lemma-regular-immersion-perfect`
(lines 16282–16334 and 16399–16416), as well as
https://stacks.math.columbia.edu/tag/068C. The section imposes no standing
Noetherian, separatedness or characteristic assumption. The lemma reduces to
a quotient by Koszul-regular generators and its finite free Koszul resolution.
The node is its closed-immersion specialization with the resolution exposed.
The source filename is more-morphisms.tex upstream; the node's longer filename
is a bibliographic pointer, not a mathematical statement error.

Edge cases: r=0 and the empty index type Fin 0 are admitted, giving I=0 and
the degree-zero ring; r=1 gives the multiplication differential. I=A and
Z empty are admitted (a unit generator gives the acyclic resolution). The
zero ring is allowed, including its free zero modules. For Y empty the
pointwise hypothesis and perfectness conditions are vacuous; the universal
local clause still covers its empty affine open, whose ring and complexes
are zero. There are no nonemptiness, Nontrivial, characteristic, field,
Noetherian or finiteness assumptions on the schemes. Both universes u and w
are explicitly declared; every object and index binder is bound.

Independent searches, using different words from the worker:

- msearch leanfinder: "finite free resolution of quotient by an ideal generated
  by a homologically regular sequence": eight regular-sequence hits, none
  stating the sheafified resolution or perfect closed immersion.
- msearch loogle: "Module.Free, QuasiIso": zero hits.
- msearch leansearch: "quotient by a Koszul regular sequence is a perfect module
  with bounded exterior power resolution": Internal Server Error; unavailable,
  no absence verdict inferred.
- rg over pinned Mathlib, WeilConjectures and lean/Sheaf for
  `perfect.*immersion|immersion.*perfect|koszul.*[Qq]uasi|[Qq]uasi.*koszul|finite free resolution`:
  the dependency definition, regular immersions over perfect fields, and
  unrelated resolution results; no existing theorem with this statement.
  rg for the full declaration name and item id in the upstream-name index,
  WeilConjectures and lean/Sheaf found no collision.

No new definition nodes, dependency modules, or statement_change are in this
delivery. None are needed: the six dependencies are usable as recorded.
No mismatch found, and no Lean or node edits made. The declaration docstring
covers the node's four proof steps (quotient sheaf, homology/augmentation,
bounded exterior-power terms and perfectness, local immersion criterion).
The sole theorem body is `by sorry`; there are no data definitions, hidden
proof holes or additional proved statements. All imports have direct uses
in the signature. Only this independent reading was appended to the report.

Validation: the unchanged module was independently compiled with scompile.py;
it returned exit code 0 with no errors or warnings. The node's lean.statement
was independently compared verbatim with the declaration signature.
