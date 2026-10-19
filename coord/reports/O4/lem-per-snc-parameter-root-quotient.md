## Worker report

The module `Sheaf.DeligneLaumon.SncParameterRootQuotient` states
`AlgebraicGeometry.exists_snc_parameter_root_quotient`, with `sorry` as its entire
proof. The natural statement, statement dependencies, and proof are unchanged.
Auxiliary definitions in the same module expand only the objects and clauses of
this statement; all have actual data and are listed in `lean.declarations`.

Source read: ILO, Travaux de Gabber, Exposé IX, Proposition 2.1 and its proof,
printed pp. 133–134 (PDF pp. 139–140), including the strict-local parameter
reduction, displayed root quotient, normalization, essential-surjectivity
paragraph, and specialization in IX 2.2. The source uses étale locality, not an
identification of a strict localization with an étale neighbourhood.

Hypotheses, individually:

* The integral regular Noetherian scheme is `(Y : Scheme.{u}) [IsIntegral Y]
  [IsNoetherian Y] (_hYregular : IsRegularScheme Y)`. Noetherian means globally
  Noetherian here, not merely locally Noetherian.
* The SNC boundary is `(T : Y.IdealSheafData)` with
  `_hT : IsStrictNormalCrossingsBoundary T`. Its open complement is exactly
  `Scheme.Opens.toScheme T.support.compl`, with inclusion `Scheme.Opens.ι`.
* The group is `{G : Type v} [Group G] [Finite G]`, with no equality of group and
  scheme universes. The exponent everywhere is `Nat.card G`, not an arbitrary
  multiple. `_hn : IsUnit (Nat.card G : Γ(Y, ⊤))` is the invertibility hypothesis,
  not a conclusion. Invertibility on the scheme is equivalent to this global
  unit condition, since the local inverses glue uniquely.
* `cover : Scheme.GaloisCoverAction G ...` supplies the finite étale surjection,
  group action and geometric torsor condition. `[ConnectedSpace cover.Z]` is
  connectedness of the total torsor space.
* `sncTorsorNormalization T cover` and its map are abbreviations for the
  published relative normalization of `cover.π ≫` the complement inclusion.
  Their only local instance is the actual `cover.isFinite` field, so the
  normalization construction can infer quasi-compactness and separation.
  This is the same normalization as in `k(V')/k(Y)`: a connected finite étale
  cover of the regular integral open is normal integral. On each affine open
  of Y, any element of its function field integral over the base is regular
  on the inverse image, by normality there; conversely integrality in that
  ring is integrality in the function field. Thus the integral closures agree.
  This uses exactly the relative-normalization construction underlying
  `Scheme.normalizationIn` in the recorded normalization dependency. No
  independent extension L, arbitrary algebra structure, or extra isomorphism
  hypothesis is supplied. `[_hfinite : IsFinite (sncTorsorNormalizationMap T
  cover)]` is precisely the finiteness assumption on the normalization map.
* `(Ω : Type u) [Field Ω] [IsAlgClosed Ω]`, the maps `ybar`, `zbar`, and `_hzbar`
  encode the geometric points and their compatibility under this map. The
  points of the torsor and its normalization are never identified.

Conclusion, clause by clause:

* The first conjunct existentially provides a ring `A : CommRingCat.{u}` with
  `IsNoetherianRing A`, `uA : Spec A ⟶ Y`, its geometric lift `uΩ`, and `r : ℕ`
  with `t : Fin r → A`. The definition `IsSncParameterRootQuotientAt` includes
  `IsRegularRing A`, `Etale uA`, and `uΩ ≫ uA = ybar`. Affineness of U is
  literal `Spec A`; no unjustified affine-morphism assumption is added.
* `IsSncParameterEquations` is evaluated on the pullback of `T.support` and
  at the point `(Scheme.SpecToEquivOfField Ω (Spec A) uΩ).1`. Its equations are
  the global sections `(Scheme.ΓSpecIso A).inv (t i)`.
* The principal zero schemes of these equations are integral, with distinct
  supports, whose union is the entire pulled-back boundary. Together with
  the germs belonging to the maximal ideal, these are exactly its components
  through the selected point; other components have been removed. This is
  scheme-theoretic component data, not just an equation for the complement.
* The maximal-ideal condition is stated on each germ. The regular-parameter
  condition is `∃ s, IsRegularSystemOfParameters (List.ofFn germs ++ s)`, so the
  boundary equations form PART of a regular system, not necessarily all of it.
* `uA ⁻¹ᵁ T.support.compl = PrimeSpectrum.basicOpen (∏ i, t i)` is the asserted
  identity `V ×_Y U = D(t₁⋯tᵣ)` as an open subscheme of U.
* `∃ ζ : Aˣ` together with `(ζ : A)^n = 1` and the universally quantified unit
  differences for `1 ≤ a < n` gives exactly the root-of-unity conditions.
* `sncParameterRootRing A n r t` is literally the multivariate polynomial ring
  modulo the ideal spanned by `X i ^ n - C (t i)`. It inherits the quotient
  A-algebra structure from Mathlib; its data contain no postponed proof.
* `H : AddSubgroup (Fin r → ZMod n)` is the specified subgroup of the additive
  exponent-vector group. `σ h` is an A-algebra automorphism, so fixes every
  coefficient. `σ 0 = AlgEquiv.refl` and the displayed addition/composition
  law give the action laws. The equation on each quotient generator is
  exactly `x_i ↦ ζ^(h_i) x_i`, using the natural representative `(h.1 i).val`.
  These coefficient and generator equations uniquely determine the rotation,
  so σ is not an unconstrained or arbitrary map.
* `⨅ h, AlgHom.equalizer (σ h).toAlgHom (AlgHom.id A B)` is the Mathlib
  subalgebra with membership exactly `∀ h, σ h b = b`. It supplies the actual
  fixed algebra and its canonical coefficient map; there is no private
  duplicate invariant-ring definition and no choice of an arbitrary A-map.
* W, `w : W ⟶` the normalization, `wU : W ⟶ Spec A`, and its geometric lift
  `wΩ` are existential. `Etale w`, `IsNoetherian W`, `wΩ ≫ w = zbar`,
  `wΩ ≫ wU = uΩ`, and `w ≫ b = wU ≫ uA` express the pointed étale
  neighbourhood, its Noetherianity and the square over b.
* `eW : W ≅ Spec (.of Bᴴ)` implies W is affine. Its final equation uses the
  canonical algebra map `A → Bᴴ`, making the isomorphism one over U.
* The second conjunct quantifies over EVERY pointed étale neighbourhood U₀,
  not only affine ones, and every supplied finite list of component equations
  near its selected point. `IsSncParameterGerms` requires the boundary equality
  only on some open neighbourhood, plus maximal-ideal membership and extension
  to a parameter system. It therefore permits other components away from the
  point. The necessary locally Noetherian instance is the actual theorem
  `LocallyOfFiniteType.isLocallyNoetherian u₀`, not an extra assumption.
  The conclusion chooses a new affine pointed refinement `q`, with `Etale q`,
  `q ≫ u₀ = uA` and `uΩ ≫ q = u₀Ω`, and exactly the same r. For EVERY i,
  `(ΓSpecIso A).inv (t i) = q.appTop (t₀ i)`, so it retains the prescribed
  equations by pullback, and all normal-form clauses hold again on this
  refinement. This does not demand that one previously chosen U refine all
  possible neighbourhoods simultaneously.
* Empty boundary forces r = 0, since each displayed component is nonempty
  integral while their union is empty. `MvPolynomial (Fin 0) A` is canonically
  A and the relation ideal is zero, so B is canonically A. `Fin 0 → ZMod n`
  is the zero group and H is its unique subgroup. These consequences of the
  stated constructions include the node's empty-boundary convention without
  excluding the case or adding a second theorem.
* No log structure on Z or chart for b is introduced.

Recorded dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, using the
  upstream `IsRegular` and Mathlib regular-local-ring/ring predicates.
* `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian` and
  `IsNoetherian`; the latter is the scheme's global Noetherian condition.
* `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `IsStrictNormalCrossingsBoundary` on `Scheme.IdealSheafData`.
* `Sheaf.AlgebraicGeometry.NormalScheme`: `Scheme.GaloisCoverAction` and its
  recorded fields; no competing Galois-cover encoding is introduced.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
* `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `Scheme.normalizationIn` / `fromNormalizationIn`, read to check that these
  are abbreviations of the same relative normalization construction used
  here. The actual general constructions used are `Scheme.Hom.normalization`
  and `Scheme.Hom.fromNormalization` from Mathlib, re-exported there.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`;
  `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.SpecToEquivOfField`.
* `Sheaf.RingTheory.IsRegularSystemOfParameters`:
  `IsLocalRing.IsRegularSystemOfParameters` on the extended list.
* `Mathlib.AlgebraicGeometry.Scheme`: `Spec`, `Spec.map`, `Scheme.ΓSpecIso`.

The module imports every currently stated proof-dependency module. The two
proof nodes `lem-per-snc-root-algebra-structure` and
`lem-per-snc-root-punctured-torsor-splitting` have neither a usable `lean`
record nor a Mathlib match at writing time, and hence provide no proof import;
they are not needed to TYPE this statement. All ten steps of the existing
natural-language proof are carried in the theorem docstring for stage 3.

Edge cases checked: r = 0; n = 1 (the unit-difference condition is empty and
`ZMod 1` gives the trivial action); arbitrary finite group universe; a point
outside the boundary; partial parameters on a higher-dimensional regular local
ring (e.g. a single coordinate divisor in a surface); multiple transverse
components; a prescribed nonaffine neighbourhood; additional components away
from the point; and possibly disconnected étale neighbourhoods (which can be
shrunk to the selected branch). A zero-ring A cannot admit the required map
from a geometric point. n = 0 never occurs because a finite group is nonempty.
No equality of site/ring/group universes or further characteristic hypothesis
is imposed. The geometric-point universe is the existing scheme-geometric-
point convention of the dependency.

Searches for an existing statement or notion:

* `msearch.py ... leansearch`, query “A connected finite etale torsor on the
  complement of a strict normal crossings divisor is etale locally a quotient
  of a root algebra”: 8 hits, including étale base change, the field étale
  algebra decomposition and `Scheme.Etale`; none gives this normal form.
* `msearch.py ... leanfinder`, query “Etale locally finite normalization in a
  torsor on a strict normal crossings complement is a fixed subring of the
  parameter root algebra”: 8 hits, including `Scheme.Hom.normalizationDiagram`
  and other relative-normalization constructions. Those existing
  constructions are reused; no theorem matches the conclusion.
* `msearch.py ... loogle`, query `FixedPoints.subring, MvPolynomial`: 0 hits.
* `msearch.py ... grep`, query
  `sncParameter|parameter_root_quotient|ParameterRoot|fixedSubring|fixedSubalgebra`:
  0 Mathlib hits. Further direct `rg` of invariant and algebra files found
  `FixedPoints.subalgebra` and `AlgHom.equalizer`; equalizers and infima are
  reused to form the fixed algebra without installing a new action instance.
* `rg` of the named upstream `WeilConjectures` tree and `lean/Sheaf` for
  parameter/root algebra names found only the characteristic-p `pthRootAlgebra`
  family and the one-variable strict-local/DVR root algebras, none this
  multivariable normal form. The former has a different exponent and the
  latter only one variable; neither is duplicated. Searching the exact item
  ID upstream returned no declaration.
* Exact proposed declaration-name searches in Mathlib, upstream,
  `dag/lean_names_upstream.json`, and `lean/Sheaf` returned no matches.
  Existing DAG root-algebra statements were inspected: they have no Lean
  record, and their conclusions are the strictly local algebra structure or
  the invariant-monoid calculation, not this pointed scheme quotient.

No `STATEMENT-DISPUTED` or source-statement correction is needed. The earlier
partial module was retained as the starting work and repaired: it had confused
the torsor with its normalization, put invertibility in the conclusion, used
only local Noetherianity for Y, required a full parameter system, omitted the
pointed étale conditions on W, and had an ill-scoped refinement placeholder.
Those are defects of the earlier draft, not changes to the DAG statement.

Validation: the prescribed `scompile.py N4 lem-per-snc-parameter-root-quotient`
compiled both its sandbox wrapper and the actual library module cleanly, with
no error or warning (3.8 seconds and 3.6 seconds respectively). Only the main
named theorem contains `sorry`; none occurs inside any definition or signature.

## Second reading by N4

Writer's second pass, not an independent-agent certification: the dispatcher
explicitly prohibits starting another agent and assigns independent review to
the maintainer after delivery. Reopened the node and the complete module and
matched every clause above. This pass caught that the prescribed neighbourhood
must be allowed to contain other components away from the point; introduced
`IsSncParameterGerms` with an equality only near that point and retained the
stronger component statement for the final shrunken affine neighbourhood.
It also checked the quantifier order: the prescribed neighbourhood and its
equations come BEFORE the choice of the refining affine neighbourhood.
The output subgroup is exactly in `(ZMod (Nat.card G))^r`, the normalization
point is separate from the torsor, W is pointed and étale, the isomorphism is
over U by its canonical map, and the empty-boundary case is retained.
No independent review is claimed in this report.
