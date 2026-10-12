## Worker report

The module retains a directed presentation of the supplied final Noetherian approximation,
aliases the landed selected separated stage/model/map, and defines epsilon by the explicit
composite `pullbackLeftPullbackSndIso.hom ≫ pullback.congrHom.hom ≫
nagataFinitePresentationDescentComparison`. There are no sorry proofs or data in this module.
No assertion of the final model's properties is folded into this definition.

Hypotheses and clauses, individually:
- The base S is `c.pt : Scheme.{u}`; its quasi-compactness and quasi-separatedness are
  `[CompactSpace c.pt]` and `[QuasiSeparatedSpace c.pt]`.
- Y is `{X : Scheme.{u}}`, its named map is `f : X ⟶ c.pt`.
- Finite presentation is `[LocallyOfFinitePresentation f] [QuasiCompact f]
  [QuasiSeparated f]`; separatedness is `[IsSeparated f]`.
- The final base system is `Q.approximation : c.pt.NoetherianApproximation`.
  `Q.reindex`, `Q.diagramIso`, and `Q.projection_eq` identify the directed presentation
  with its stages and projections. `hc : IsLimit c` certifies the retained limit.
  No equivalence of a general cofiltered category with a preorder is assumed.
- I is `Type u`, `[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`.
  D is `Iᵒᵖ ⥤ Scheme.{u}` and every `D.map t` has `IsAffineHom`.
- `i₀` and the compact/quasi-separated stage instances are the initial and valid bases
  needed by the recorded chain. They are inherited from the identified Noetherian stages.
- `R`, `P`, `A` retain the relative gluing choices, raw inclusions and valid stage data.
  `G`, `B`, `E` retain the finite-presentation gluing, base map and comparison data.
  Each uses the landed dependency definition; none is a private replacement.
- The comparison `IsIso` instance and the descended map's locally-finite-presentation,
  quasi-compact and quasi-separated instances are input properties of the constructed
  finite-presentation model, proved separately by its predecessor lemma; they are not
  assumptions about the newly selected later model.
- lambda_Y is `nagataFinalDescendedStage`, definitionally the existing
  `nagataSeparatedDescentStage` with the same inputs.
- Y_lambda is `nagataFinalDescendedModel`, definitionally the existing
  `nagataSeparatedDescentModel` with the same inputs.
- Its structure map is `nagataFinalDescendedMap`, the existing separated projection.
- epsilon has source `pullback (nagataFinalDescendedMap …)
  (c.π.app (op (nagataFinalDescendedStage …)))` and target X.
  Reassociation first gives the pullback along the composite projection and transition;
  `c.w` equates this to the valid-stage cone projection; then E.comparison maps to X.

Dependencies read and used:
- `Sheaf.AlgebraicGeometry.GluedLimitComparison`:
  `Scheme.NoetherianApproximation.gluedLimitComparison`; the underlying approximation
  is upstream `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
- `Sheaf.AlgebraicGeometry.NagataSeparatedDescentStage`:
  `nagataSeparatedDescentStage`, `nagataSeparatedDescentTransition`,
  `nagataSeparatedDescentModel`, `nagataSeparatedDescentMap`.
- Its landed predecessor `NagataFinitePresentationDescent`:
  `NagataFinitePresentationGluingData`, `NagataFinitePresentationBaseMap`,
  `NagataFinitePresentationComparisonData`, `nagataFinitePresentationDescentMap`,
  `nagataFinitePresentationDescentComparison`.
- The entire `NagataRelativeGluingDatumDescent` and the valid-stage declarations were read;
  all datum inputs use them through the landed imports.
- `Sheaf.AlgebraicGeometry.FinalNoetherianBaseSystemProperties`:
  `Scheme.NoetherianApproximation.finalBaseSystem_properties` was read. Its properties
  are not asserted by this definition; the approximation's upstream instances supply
  stage Noetherianity and affine transitions. No unused import of that theorem is added.
- Mathlib `CategoryTheory.Limits.pullbackLeftPullbackSndIso`, `pullback.congrHom`;
  `Cone.w` supplies the equality needed to identify the two pullbacks.

Edge cases checked: the empty scheme is allowed; the initial stage prevents an empty
index set, as required by the chain, rather than arbitrarily excluding one. No assumption
of a nonempty chart set, reducedness, characteristic, or a nonzero ring is added.
I and schemes share universe u. A general cofiltered category need not be thin, which
is why the directed presentation and its actual diagram identification are recorded.
Repeated stages, identity transitions and singleton directed systems are allowed;
the comparison is still the canonical iterated-pullback composite in those cases.
The identification Q intentionally does not affect the selected gluing choices: it
certifies that their base diagram is the final Noetherian system. All model data are
fixed by the existing definitions, not unconstrained fields or choice from sorry.

Searches made with msearch.py:
- LeanFinder: "separated descended finite presentation model over a Noetherian
  approximation with constructed base change comparison"; eight hits on smooth algebra
  descent and finite presentation, none the requested construction.
- Loogle: `pullbackRightPullbackFstIso`; unknown identifier at the external service.
- grep: `finalDescended|FinalDescended|pullbackRightPullback` in CategoryTheory;
  nine generic pullback-pasting references, no final Nagata construction.
- LeanSearch: "separated descended model of finite presentation over a Noetherian
  approximation"; service unavailable (Internal Server Error).
- rg in Mathlib's Pullback sources located the exact pasted-pullback isomorphism and
  `pullback.congrHom`; their full signatures were read.
- rg `finalDescended|FinalDescended|def-nagata-final-descended-model` over the upstream
  WeilConjectures and landed Sheaf source returned no existing final construction.

Compilation: the local library has not yet refreshed the newly landed
NagataSeparatedDescentStage. The permitted server fallback compiled this single module
cleanly in 2.1 seconds, including its object output. After the local library refresh, lcompile.py also compiled the module cleanly in 2.3
seconds. deliver2.py --no-push printed OK: server compile and preflight pass, with only
the independent second-reading section intentionally left for the separate reader.
Nothing was pushed.

## Statement corrected

The original statement was:

Let $S$ be quasi-compact and quasi-separated and let $Y\to S$ be
separated and of finite presentation.
Apply the separated-descent construction to
$Y\to S$ relative to $\mathsf N_f=\mathsf N(S)$. Define

$$
\lambda_Y=\lambda_{\mathrm{sep}}(Y/S),
\qquad
Y_{\lambda_Y}
=Y^{\mathrm{sep}}_{\lambda_Y},
$$

and let

$$
\epsilon_Y\colon
Y_{\lambda_Y}
\times_{S_{\lambda_Y}}S
\longrightarrow Y
$$

be the constructed base-change comparison.

The upstream approximation indexes an arbitrary cofiltered category, while the landed
separated construction requires a directed preorder. It cannot be applied directly with
only the original notation N(S). The corrected node explicitly retains the directed
presentation and its identification with N, together with the predecessor's constructed
choices and properties, and specifies the comparison by pullback reassociation. This
follows blueprint orders 371--373 and the neighbouring separated and finite-presentation
construction, without changing the final assembly's mathematical objects or properties.
The original blueprint node text supplied by the launcher is the available source text.
The correction is an interface clarification, not an assertion of the existence of a
new presentation or an automatic choice of unproved gluing data. Such existence belongs
to the predecessor construction.

- def-nagata-final-basechanged-compactification: holds. The same selected structure map and explicit comparison supply its base change and inverse once isomorphy is proved.
- lemma-nagata-final-descended-model: holds. The selected model and comparison are unchanged; stage Noetherianity transfers across the recorded stage isomorphism.
- def-nagata-final-noetherian-compactification: holds. The same selected model over the identified Noetherian stage supplies its Noetherian compactification.
- lemma-weil-pbc-chow-factorization: holds. Its proof-only citation remains a finite-presentation descent construction; the Chow statement is unchanged.

## Second reading by Z2

The node clauses are: a quasi-compact, quasi-separated base; a separated finite-presentation
map `Y ⟶ S`; the final Noetherian approximation in directed form; the selected index
`λ_Y`; its descended model and structure map; and the constructed comparison from the
pullback to `Y`.  These render as `c.pt` with `[CompactSpace c.pt]`
`[QuasiSeparatedSpace c.pt]`, `f` with `[IsSeparated f]`
`[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`,
`NagataFinalBaseSystemIdentification`, `nagataFinalDescendedStage`,
`nagataFinalDescendedModel`, `nagataFinalDescendedMap`, and
`nagataFinalDescendedComparison`.  The directed system uses `I : Type u`,
`[Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]`, affine transitions, and a limit cone.

The original prose did not specify how the arbitrary approximation `N(S)` is presented in
the directed-preorder form required by the landed separated construction, nor how epsilon is
reassociated.  The Lean supplies these through `NagataFinalBaseSystemIdentification` and
the explicit composite with `pullbackLeftPullbackSndIso` and `pullback.congrHom`; this is
recorded as the node's statement correction.  No property lemma is folded into the
definition.  Empty schemes, singleton or repeated stages, identity transitions, and all
universes remain covered; no characteristic, reducedness, or nonzero-ring assumption is
added.  Searches found no existing declaration.  `lcompile.py` compiles the module cleanly.
