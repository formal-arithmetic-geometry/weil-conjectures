## Worker report

Module: `Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom`.
Declaration: `AlgebraicGeometry.Scheme.isIso_homComplex_resolution_of_isStrictlyPerfect`.
One theorem, with proof `sorry`; no definition or instance added.

Hypothesis and conclusion correspondence:

- The affine scheme U is `U : X.Opens` with `[IsAffine U.toScheme]`. This is the
  localized-site presentation used by the recorded strictly-perfect predicate. Any
  standalone affine scheme occurs by taking X to be that scheme and U its top open;
  conversely any such open is an affine scheme. No condition is placed on ambient X.
- P is a complex of O_U-modules: `P : CochainComplex (SheafOfModules.{u}
  ((moduleRings X.toRingedSpace).over U)) ℤ`.
- Strict perfectness, boundedness, and finite projective terms are exactly
  `_hP : IsStrictlyPerfect X U P`. The recorded definition has bounds a,b and
  retractions onto finite free modules in every degree, including zero terms.
- “For every complex M” is the unrestricted binder M of the same cochain-complex
  type. M is not assumed bounded, quasi-coherent, projective or injective.
- “Derived internal Hom” is the recorded `derivedInternalHom` on the over-site
  `((Opens.grothendieckTopology X).over U)` with commutative structure sheaf
  `X.sheaf.over U`, evaluated on `(op (Q.obj P), Q.obj M)`.
- “Represented by the ordinary Hom complex” is the first conjunct, `Nonempty
  (Q.obj (homComplex P M) ≅ derivedInternalHom ... .obj ...)`.
- “The canonical comparison ... is an isomorphism” is the second conjunct.
  It quantifies over a functorial replacement I, its augmentation η, and its
  defining condition `∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective`.
  For each computation isomorphism e from RHom(QP,QM) to QHom(P,I(M)), it asserts
  `IsIso (Q.map (((homComplexFunctor ...).obj (op P)).map (η.app M)) ≫ e.inv)`.
  This is the canonical map induced by the resolution, transported to RHom.
  In particular take e to be the component of `derivedInternalHom_comparison`.
  Quantifying over e does not strengthen invertibility: composing with any
  isomorphism preserves and reflects it. Replacement choices are quantified in
  the conclusion, not additional restrictions on M. Their existence and the
  existence of e are supplied by the recorded RHom construction.
- The explicit `HasDerivedCategory.{w}` binder is the localization infrastructure,
  in precisely the sheaf-compose encoding required by `derivedInternalHom`.
  This compiles with P and M on the recorded localized module carrier. Universes
  u and w are explicit, and there are no auto-bound variables or file-local aliases.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsStrictlyPerfect`.
- `Sheaf.Algebra.Homology.DerivedInternalHom`: `CategoryTheory.derivedInternalHom`
  and its `derivedInternalHom_comparison` computation (explained in the docstring).
- `Sheaf.AlgebraicGeometry.DerivedCategory` (imported through PerfectComplex):
  the same `DerivedCategory` of `SheafOfModules` as `schemeDerivedCategory`.
- `Sheaf.Algebra.Homology.HomComplex` (imported through DerivedInternalHom):
  `CategoryTheory.homComplex` and `CategoryTheory.homComplexFunctor`.
  These are already carried by def-pur-hom-complex, reached through the RHom node;
  no new notion or dependency module is needed.

Source checked: https://stacks.math.columbia.edu/tag/08DM, Lemma 20.46.9.
The local literature checkout lacks cohomology.tex; the authoritative Stacks page
was read instead. The affine hypothesis is the node's specialization of that lemma.
The docstring carries every step of the DAG proof: K-injective replacement,
finite-projective exactness from finite-free internal Hom, bounded stupid filtration,
long exact sequence and five lemma, and localization plus independence.

Edge cases: P=0, zero terms (rank zero summands), M=0, arbitrary unbounded M,
negative degrees, and the empty affine scheme are all included. No nonempty-open
or rank-positive hypothesis is imposed. The Hom complex remains the recorded
product-valued construction; bounded P makes the potentially nonzero factors finite.
No characteristic or coefficient restriction is imposed.

Searches:

- msearch.py LeanFinder: “derived internal Hom from a strictly perfect bounded
  complex equals the ordinary sheaf Hom complex”: eight generic Ext/derived-category
  hits, no sheaf-valued strictly-perfect comparison.
- msearch.py Loogle: “CochainComplex, IsIso”: zero hits; unknown identifier IsIso.
- msearch.py Mathlib grep: `strictlyPerfect|StrictlyPerfect|RHom` in CategoryTheory:
  returned unrelated Hom names, no match.
- msearch.py LeanSearch: “derived sheaf internal Hom from bounded finite projective
  complex”: unavailable, Internal Server Error.
- rg on lean/Sheaf and WeilConjectures for RHom, rhom, derivedInternalHom and
  homComplex found the recorded constructions and distinct pro-etale/abstract
  monoidal statements, no theorem stating this sheaf-Hom comparison.
- grep for the exact node id in WeilConjectures: no hit.
- rg for the proposed full declaration in Mathlib, WeilConjectures, lean/Sheaf
  and dag/lean_names_upstream.json: no collision.
- Read WeilConjectures/CategoryTheory/DerivedCategory/Perfect.lean: its perfect
  dual tensor comparison is an abstract monoidal derived-category theorem,
  not the ordinary sheaf Hom-complex calculation of this node.

No statement correction, new node, unusable dependency, or statement dispute.
Server compilation is the validation; nothing is compiled on this machine.

## Second reading by K1

I reread the node, its Stacks source (Tag 08DM, Lemma 20.46.9), all three
statement dependencies, and the submitted module. The correspondence is:

- The affine scheme is rendered by `(X : Scheme.{u}) (U : X.Opens)` and the
  instance `[IsAffine U.toScheme]`; this is the localized affine presentation
  used by `IsStrictlyPerfect` and introduces no extra geometric hypothesis.
- The two complexes of `O_U`-modules are the explicit binders `P M` of type
  `CochainComplex (SheafOfModules ((moduleRings X.toRingedSpace).over U)) ℤ`.
- Strict perfectness is exactly `_hP : IsStrictlyPerfect X U P`, whose recorded
  definition supplies boundedness and finite-free direct-summand terms.
- The derived category infrastructure is exactly the displayed
  `[HasDerivedCategory.{w} ...]` instance required by `derivedInternalHom`.
- The representation clause is the first conjunct, the `Nonempty` isomorphism
  between `Q.obj (homComplex P M)` and the value of `derivedInternalHom`.
- The canonical comparison clause is the second conjunct: for every functorial
  replacement `I`, augmentation `η`, and hypothesis
  `∀ N, QuasiIso (η.app N) ∧ (I.obj N).IsKInjective`, every computation isomorphism
  `e` yields `IsIso` for the localized Hom-complex map followed by `e.inv`.
  This is the explicit form of the canonical comparison supplied by
  `derivedInternalHom_comparison`; it adds no assumption on `M`.

The source itself allows arbitrary ringed spaces and arbitrary second complexes;
the node intentionally specializes the first to an affine open and the Lean
statement preserves the unrestricted `M`. Empty opens/schemes, `P = 0`, zero
finite-free ranks, `M = 0`, unbounded `M`, negative degrees, `n = 0`, and every
characteristic are covered. No nonemptiness, positive-rank, Noetherian, or field
characteristic hypothesis is present. Universes `u` and `w` are explicit and
the index of the complex is the fixed `ℤ` required by the source construction.

I searched Mathlib, `WeilConjectures`, and `lean/Sheaf` with LeanFinder,
Loogle, LeanSearch, and `rg` for strictly-perfect derived internal Hom and
the exact declaration; only the recorded generic constructions were found.
No duplicate notion or existing theorem is available.

No mismatch was found. The module was unchanged: its signature is verbatim in
the node's `lean.statement`, contains no unbound variables or local notation,
and has only the permitted `sorry` proof. Compilation with
`scompile.py K1 lem-pc-rhom-strict-perfect-hom` completed successfully.
