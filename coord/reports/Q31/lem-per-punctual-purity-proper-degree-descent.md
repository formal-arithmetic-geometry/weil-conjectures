## Worker report

The module `Sheaf.AlgebraicGeometry.PunctualPurityProperDegreeDescent` states
`AlgebraicGeometry.Etale.punctual_purity_of_proper_primeToDegree`. Its only declaration
is this named theorem, with a single `sorry` and the node's seven-step proof in its
docstring. Both purity conditions use the existing
`AlgebraicGeometry.Etale.IsPunctuallyPure` from
`Sheaf.AlgebraicGeometry.PunctualPurity` (`def-per-punctual-purity`).

This repairs the independent return on immutable head `17e7204e12b5`, H4/H12:

- Deleted `punctualPurityClassFamily`, `PunctualPurityClassIsIso`,
  `IsCohomologicallyPunctuallyPureAt`, and `IsCohomologicallyPunctuallyPure`.
- Imported `Sheaf.AlgebraicGeometry.PunctualPurity` and used its predicate in `hpure`
  and the conclusion. The node's `lean.declarations` now lists only the theorem.
- Recorded the requested §1(C) `statement_change`: the opening paragraph now cites
  `def-per-punctual-purity` instead of defining its notion inline; `stmt_deps` gains
  precisely that node. The geometric hypotheses, proof and proof dependencies are
  unchanged. No new node or dependency module is delivered.

The saved packet was read before the initial unchanged `deliver2.py --no-push`.
That dry run passed as commit `aa0f73732b`; it was not pushed because the supplied
return still required the canonical-definition repair. The older source/interface
publication failures in the saved report no longer occur. That historical report
is retained only in the sandbox scratchpad, not delivered.

Each hypothesis and clause is rendered as follows:

- Prime and coefficients: `(ℓ : ℕ) (hℓ : ℓ.Prime)`; the imported purity definition
  uses `regularClassCoefficients ℓ 1`, the universe lift of `ZMod (ℓ ^ 1)`.
- Ordinary small-etale categories and Tate twists: the imported predicate's
  `punctualPurityClassMap` lies in the existing `DerivedCategory.Plus` of ordinary
  small-etale module sheaves and uses `regularClassTwist`. There is no pro-etale
  or adic coefficient category.
- The local scheme, dimension and closed point: in `IsPunctuallyPureAt`,
  `Spec (W.presheaf.stalk w)`, `ringKrullDim (W.presheaf.stalk w) = d`, and
  `Spec.map (W.residue w)` are the actual objects in the node.
- The canonical local map: `punctualPurityClassMap` transposes the level-1,
  untensored supported class through the published closed-support adjunction
  and exact direct-image comparison. Its family `regularImmersionClasses` is
  chosen from the uniquely specified class calculus. Purity is `IsIso` of that
  transpose. The structural witnesses in `IsPunctuallyPureAt` record finite
  dimension, local Noetherianity, regular immersion and coefficient invertibility;
  they are automatic here, independently of purity.
- Every point: `IsPunctuallyPure ℓ hℓ T` means
  `∀ w : T, IsPunctuallyPureAt ℓ hℓ T w`, including nonclosed points of T.
- Trait: `(R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]`.
  The existing DVR class is the nonfield local PID condition, equivalent to the
  node's Noetherian local domain of dimension one with principal maximal ideal.
- Strict henselianity: `[IsStrictlyHenselianLocalRing R]` is the existing
  henselian local ring with separably closed residue field.
- Completeness: `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]`.
- Mixed characteristic: `[CharZero (FractionRing R)]` and
  `(hres : 0 < ringChar (IsLocalRing.ResidueField R))`.
- Invertible prime on S: `(hℓR : IsUnit (ℓ : R))`.
- The common base S: `[V.Over (Spec (.of R))] [W.Over (Spec (.of R))]`;
  `[f.IsOver (Spec (.of R))]` states that f is a morphism over S.
- Integral and regular: `[IsIntegral V] [IsIntegral W]`,
  `(hV : IsRegularScheme V) (hW : IsRegularScheme W)`.
  The recorded regular predicate includes local Noetherianity and regular stalks.
- Finite type: `LocallyOfFiniteType` and `QuasiCompact` of both structure maps.
  Together with the Noetherian affine DVR base these imply Noetherianity.
- Quasi-projectivity: `hVqp` and `hWqp` exhibit `N : Type u`, `Finite N`,
  an immersion into `ℙ(N; Spec (.of R))`, and equality of its composite structure
  map with the given structure map. `IsImmersion` means locally closed immersion.
  This retains the node's exact projective-space convention over this trait;
  the existing field-only `IsQuasiProjective` predicate does not apply here.
- Proper and dominant map: `(f : V ⟶ W) [IsProper f] [IsDominant f]`.
- Generic degree: `(d : ℕ)`, `(hd : 0 < d)` and `(hprime : ¬ ℓ ∣ d)`.
- The nonempty generic finite-etale locus: `hgeneric` exhibits `U : W.Opens`,
  `Nonempty U`, `IsFinite (f ∣_ U)`, `Etale (f ∣_ U)` and the published
  `(f ∣_ U).IsFiniteLocallyFreeOfDegree d`.
- Source purity and target purity: `(hpure : IsPunctuallyPure ℓ hℓ V)` and
  conclusion `IsPunctuallyPure ℓ hℓ W` use literally the same published predicate.
  No flatness hypothesis is present on f.

Dependencies reused, with their recorded modules and declarations:

- `Sheaf.AlgebraicGeometry.PunctualPurity`:
  `AlgebraicGeometry.Etale.IsPunctuallyPure`, `IsPunctuallyPureAt`,
  `punctualPurityClassMap`, `regularImmersionClasses`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficients import:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`, used via `regularClassTwist`.
- `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `regularClassCoefficients`, `regularClassTwist`, `RegularImmersionClassFamily`,
  `regular_immersion_class_calculus`, used through the canonical purity definition.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `Scheme.residue`;
  `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`;
  `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`;
  `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral`;
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` supplies
  `Scheme.Hom.IsFiniteLocallyFreeOfDegree`; the projective-space, immersion,
  henselian, adic-complete and DVR imports supply the remaining existing notions.

All six recorded proof-dependency modules are non-public imports: compact support,
exceptional adjunction, proper projection formula, open exchange, compact-support
projection under open restriction, and trait-dualizing scalar restriction. The
three proof nodes for prepurity lci classes, the relative-class criterion and
finite-etale derived ambidexterity still have no recorded Lean module on the base;
there is no such import to add. They remain explicit in the theorem's proof docstring.

Edge cases checked: codimension zero and generic points remain in the canonical
local test; finite local dimension is witnessed, never truncated. Degree one is
included, degree zero and degrees divisible by ℓ are excluded exactly by `hd` and
`hprime`. Integral schemes are nonempty and the generic open is explicitly
nonempty. An empty coordinate type cannot supply a projective immersion for an
integral nonempty scheme but need not be excluded syntactically. Positive residue
characteristic and invertibility of ℓ exclude the residue characteristic prime.
The new predicate does not add a geometric assumption or remove a local point.

Searches, including the repair checks:

- `msearch.py leanfinder`, query “Proper prime to ell degree descent of cohomological
  punctual purity over a strictly henselian trait”: residue-field and local/henselian
  declarations, no descent theorem.
- `msearch.py loogle`, query
  `IsDiscreteValuationRing, IsStrictlyHenselianLocalRing, IsAdicComplete`: no hits;
  the upstream strict-henselian identifier is absent from its Mathlib index.
- `msearch.py grep`, query
  `punctual.*pur|IsQuasiProjective|IsAdicComplete|IsDiscreteValuationRing`: 25
  reported hits on DVRs, completeness and related instances, no descent theorem.
- Earlier LeanSearch query “cohomological punctual purity local regular scheme
  Kummer fundamental class”: no descent theorem (residue/local-algebra hits).
- `rg` on upstream `WeilConjectures` and shared `lean/Sheaf` for
  `punctual_purity_of_proper_primeToDegree|IsPunctuallyPure`: upstream weight-purity
  hits are a different notion; shared `PunctualPurity.lean` supplies exactly the
  required cohomological predicate. `SmoothPunctualPurityAscent.lean` and
  `LogSmoothTraitPunctualPurity.lean` already use it. The four local definitions
  therefore were duplicates and have been removed, as required by H4/H12.
- DAG search for the item ID, followed by checking `stmt_deps` and `proof_deps`,
  found precisely the direct citer listed below. Mere mentions in ancestry and
  correction history do not create additional direct citers.

The source PDF was read locally through `pdftotext`: ILO XVI Definitions
3.2.1--3.2.2, p.244, explicitly define punctual purity by the local class being an
isomorphism; Proposition 3.5.7, pp.249--250, descends that same notion along the
proper invertible-degree map. The canonical definition's D+ transpose is exactly
this map. No mathematical statement dispute is raised for this item. The imported
class-calculus theorem retains its author's uniqueness concern; this repair uses
its recorded declaration without modifying that dependency.

## Statement corrected

Old statement, verbatim:

For a prime $\ell$ and $A=\mathbf F_\ell$, use ordinary small-etale derived categories and Tate twists [def-weil-pbc-derived-categories, def-asd-finite-etale-tate-twist]. If $W$ is a regular Noetherian scheme with $\ell$ invertible [def-weil-regular-scheme], say that $W$ is punctually pure at $w\in W$ when, for $W_w=\operatorname{Spec}\mathcal O_{W,w}$, $d_w=\dim\mathcal O_{W,w}$ and its closed-point inclusion $j_w:\operatorname{Spec}\kappa(w)\hookrightarrow W_w$, the Kummer fundamental-class map
$$A_{\kappa(w)}\longrightarrow j_w^!A_{W_w}(d_w)[2d_w]$$
of [lem-per-regular-immersion-class-calculus] is an isomorphism. Say that $W$ is punctually pure when this holds at every point. Local rings and residue fields are as in [def-weil-residue-field], affine spectra as in [def-weil-affine-spectrum], and dimension as in [def-weil-pbc-krull-dimension-ring].

A trait here is $S=\operatorname{Spec}R$ for a discrete valuation ring: a Noetherian local domain of dimension one whose maximal ideal is principal. A complete strictly henselian trait has $R$ complete for its maximal-ideal topology and henselian with separably closed residue field (henselian means that every simple root over the residue field of a monic polynomial over $R$ lifts to a root over $R$). Mixed characteristic means that $\operatorname{Frac}R$ has characteristic zero and the residue field has positive characteristic.

Let $S$ be a complete strictly henselian mixed-characteristic trait on which $\ell$ is invertible. Let $f:V\to W$ be a proper dominant $S$-morphism of integral regular schemes of finite type and quasi-projective over $S$ [def-weil-proper-morphism, def-pc-integral-scheme, def-weil-finite-type-morphism]. Quasi-projective means admitting a locally closed immersion into a finite-dimensional projective space over $S$. Suppose that $f$ is generically finite etale of positive degree $d$ not divisible by $\ell$, meaning finite etale of degree $d$ over a nonempty open subscheme of $W$. If $V$ is punctually pure, then $W$ is punctually pure. No flatness hypothesis on $f$ is imposed.

The inline definition duplicated the already owned ILO XVI punctual-purity notion.
The prior Lean made a second, non-definitionally-equal Yoneda predicate. The
correction replaces only that introductory definition with the reference
`[def-per-punctual-purity]` and adds that node to `stmt_deps`. It follows ILO XVI
Definitions 3.2.1--3.2.2, p.244, and Proposition 3.5.7 with Lemmas 3.5.8--3.5.10,
pp.249--250, in the section 3.7 trait specialization. All other clauses stay as
accepted in the return. The prior `stmt_deps` are recorded verbatim in
`statement_change.old_stmt_deps`; proof and proof dependencies are unchanged.

Complete direct-citer audit:

- `lem-per-gabber-regular-pair-purity`: **holds: true**. Step 4 still applies descent
  to the proper generically finite-etale prime-to-ℓ alteration, with the same
  geometric assumptions. Its punctual-purity premise and conclusion now use the
  canonical predicate also used by smooth ascent and log-smooth trait purity.
  No citer is edited and none breaks.

## Second reading by Q31

Author's second reading only: the dispatcher prohibits starting another agent;
the maintainer supplies independent review. I reopened the corrected node,
canonical definition and theorem side by side. The only semantic-interface
mismatch identified by the return was the duplicate purity predicate. There is
now exactly one delivered declaration, and both its purity expressions are
`IsPunctuallyPure ℓ hℓ`. I checked the prime, trait, completeness, mixed
characteristic, invertibility, both base structures, integral/regular hypotheses,
both finite-type and immersion conditions, proper dominance, positivity,
prime-to-degree condition and nonempty finite-etale locus against the corrected
node. Each has the rendering listed above. No extra flatness or global
Noetherian hypothesis was added. The canonical local definition includes every
point and the actual residue quotient, dimension and transpose class.

Comparison with the retained returned packet and current base: the four helper
definitions and their metadata are removed; the canonical module replaces their
owning import; the theorem's two purity terms are replaced; its module and final
proof-step documentation are updated; and the required source-based statement
correction is recorded. Other node fields agree with the current shared base,
and the seven-step proof and proof dependencies agree verbatim.

Validation: the prescribed `scompile.py` compiles the repaired file separately
in both sandbox and library forms, exit 0, 5.1 s and 5.6 s, without warnings.
All variables and the universe are explicitly bound (`autoImplicit false`);
there is one named postponed theorem and no delivered definitions. No Lean line
exceeds 100 characters. The node's recorded signature is verbatim from its module.
