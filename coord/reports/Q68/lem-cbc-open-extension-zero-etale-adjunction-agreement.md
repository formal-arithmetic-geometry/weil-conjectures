## Worker report

The module `Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement`
defines the specified comparison `AlgebraicGeometry.Etale.openImmersionToEtaleLowerShriek`
and states `AlgebraicGeometry.Etale.openImmersionToEtaleLowerShriek_adjunction_agreement`.
The only postponed proof is that named theorem, whose docstring gives all six proof
steps of the DAG node. No node statement is changed and no new node is required.

Hypothesis and clause correspondence:

- A commutative coefficient ring is `(Λ : Type (u + 1)) [CommRing Λ]`.
- Schemes and the open immersion are `{U X : Scheme.{u}} (j : U ⟶ X)
  [IsOpenImmersion j]`. Etaleness is obtained by the recorded Mathlib instance,
  with no additional etaleness assumption.
- The module-sheaf categories are `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)`
  and its X analogue. These are sheaves with sectionwise Λ-linear maps and the
  usual small-etale topology, using the established constant-module-valued encoding.
  The universe u+1 is the coefficient size of the recorded six-functor interfaces;
  it adds no finiteness, nonzero-ring, or scheme hypothesis.
- Open extension is `openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j`, and etale
  extension is `etaleLowerShriek (ModuleCat.{u + 1} Λ) j inferInstance`.
- The common inverse image is `upperStar (ModuleCat.{u + 1} Λ) j`.
  The respective specified adjunctions are `openImmersionLowerShriekUpperStarAdjunction`
  and `etaleLowerShriekUpperStarAdjunction`, rather than arbitrary witnesses of adjointness.
- The specified presheaf inclusion and its sheafification are the actual data of
  `openImmersionToEtaleLowerShriek`. Unfolding the recorded definitions, BOTH presheaf
  extensions are `localizationLowerShriekPresheaf ... =
  (MorphismProperty.Over.map ⊤ inferInstance).op.lan`; BOTH sheaf extensions are
  `sheafToPresheaf ... ⋙ that lan ⋙ presheafToSheaf ...`.
  Consequently the single-summand inclusion in the node is the identity on this
  shared model of the presheaf extension. The definition applies `Functor.whiskerRight`
  to that identity and `presheafToSheaf`, so it is literally its sheafification,
  as a natural transformation in F. This uses no choice of a map from an existence
  theorem, no abstract uniqueness-of-left-adjoints comparison, and no new copy of
  an extension functor. The single-lift and direct-sum section descriptions are the
  two interpretations of the SAME recorded lan, not independently implemented
  presheaves. The empty/terminal comma descriptions can also be read in upstream
  `CategoryTheory/GrothendieckAbelian/HasLeftKanExtension.lean`, LiftIndex section.
- The natural-isomorphism assertion is `IsIso (openImmersionToEtaleLowerShriek Λ j)`.
  Naturality itself is part of the defined natural transformation, and `IsIso`
  asserts that it admits an inverse natural transformation.
- For EVERY F, G and α, the second conjunct equates the inverse `homEquiv` of the
  open adjunction to `κ.app F ≫` the inverse `homEquiv` of the etale adjunction.
  Thus it is the required equality of transposes with the specified κ and has
  exactly the direction in the node.
- The third conjunct, for every F, is
  `η_et.app F = η_open.app F ≫ upperStar.map (κ.app F)`.
- The fourth conjunct, for every G, is
  `ε_open.app G = κ.app (upperStar.obj G) ≫ ε_et.app G`.
  Lean composition order `≫` reverses the usual displayed function-composition order,
  so these are exactly both last equations of the node.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion` (def-weil-open-immersion).
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: the instance `[IsOpenImmersion j] :
  Etale j` (lem-weil-pbc-open-immersion-etale; its mathlib_match gives this instance).
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently `SheafOfModules`, for the general ringed-site category dependency.
  The constant-coefficient specialization uses the ModuleCat-valued encoding already
  used by all the recorded extension and inverse-image declarations, rather than
  introducing another category or constant ring sheaf.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`,
  `localizationLowerShriekPresheaf`, and
  `openImmersionLowerShriekUpperStarAdjunction`, for the open extension and adjunction.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar` for inverse image.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek` and
  `etaleLowerShriekUpperStarAdjunction` for the sum extension and its adjunction.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`. Read using
  `scompile.py --source`, because the stale local checkouts lack its file. Its two
  etale adjunctions are exactly the ones named here. Publicly importing this module
  supplies the recorded six-functor dependencies and retains that precise connection.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`; the comparison definition uses `presheafToSheaf` directly.
- Proof dependency `lem-weil-pbc-adjunction-of-natural-bijection` is Mathlib's
  `CategoryTheory.Adjunction.mkOfHomEquiv`, read with `CoreHomEquiv` and the unit/counit
  formulas in `Mathlib.CategoryTheory.Adjunction.Basic`, already in the import closure.
  All other proof dependencies are also statement dependencies present in that closure.

Source and edge checks:

Read Stacks `sites-modules.tex`, lemma-extension-by-zero (03DI), including its
summandwise construction of α -> α', and `etale-cohomology.tex`,
definition-extension-zero (03S3), its following Hom characterization, and
equation-j-p-shriek. These give exactly the stated presheaf construction and
canonical adjunctions. Read both complete recorded adjunction implementations:
they transport the same sheafified-lan adjunction by the same
`upperStarIsoLocalizationRestriction`.

Checked j = identity, U empty, X empty (hence U empty), F zero, G zero and Λ the
zero ring. The map is always the sheafification of the prescribed identity in the
shared model; none of these cases is excluded. For a test object with no lift,
the presheaf is zero and the comparison is its unique map. This includes a
restriction from such an object to one admitting a lift: both restriction maps
have zero source. For a lift, the identity maps the unique summand identically.
No nonempty-index assumption or chosen lift occurs in the statement.

Searches for an existing exact statement (2026-10-17):

- msearch.py LeanFinder: "For an open immersion the single lift extension by zero
  agrees with the sum over etale lifts and their adjunctions". Eight results about
  `IsOpenImmersion.lift` and its properties; none is the comparison statement.
- msearch.py Loogle: `CategoryTheory.Adjunction.leftAdjointUniq`. Twelve results on
  abstract left-adjoint uniqueness and unit/counit formulas. These do not identify
  the specified single-summand/sheafification map, so are not an exact match.
- msearch.py LeanSearch: "Extension by zero along an open immersion agrees with
  etale extension by zero compatibly with their adjunctions". Eight hits about
  scheme module restriction adjunctions or extension of functions; no exact match.
- msearch.py Mathlib grep `extensionByZero|lowerShriek|extension.by.zero` in
  `AlgebraicGeometry/Sites`: zero hits.
- rg in upstream WeilConjectures and side `lean/Sheaf` for the item id,
  `openImmersion.*[Ee]tale`, `etaleLowerShriek.*openImmersion`: related extension,
  base-change, constructibility and pro-etale comparison declarations only; no
  declaration comparing these two particular adjunctions via this specified map.
  The upstream EtaleMap docstring notes the open-immersion specialization but
  contains no theorem with the node's assertion.
- rg of Mathlib, upstream and side sources for
  `openImmersionToEtaleLowerShriek`: no hits (name is available).

No disputed statement or node fault was found. No dependency record repair,
new node, or statement correction is needed.

## Second reading by Q68

Final worker self-check: reopened the node and finished file and matched every
binder and all four conjuncts as above. The dispatcher expressly prohibits
starting another agent; this is not represented as an independent worker review.
The maintainer's independent delivery review remains the independent check.

The specified κ is constructed before its theorem by sheafifying the identity
of the common presheaf model; it is not an arbitrary compatible isomorphism.
The theorem binds all F, G and α, and both units and counits belong to the same
recorded adjunctions as the transposes. No hypothesis on a test object or a
chosen lift has slipped into the theorem. The zero and unique-summand cases
are both covered. The first compiler run found only projection line-break
syntax errors, which were fixed; no mathematical change resulted.
