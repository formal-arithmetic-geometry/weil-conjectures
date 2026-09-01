/-
Shared prelude for the Verso blueprint of Nagata's compactification theorem.

Importing `WeilConjectures` here makes every declaration of the project visible to the
chapter modules, so that the `(lean := "...")` attachments of the Blueprint nodes resolve
to real declarations and the progress summary can report on them.
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Macros

import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.DisjointnessBlowup
import WeilConjectures.Blowup.EliminationOfIndeterminacy
import WeilConjectures.Blowup.Extension
import WeilConjectures.Blowup.FiniteDegree
import WeilConjectures.Blowup.Gluing
import WeilConjectures.Blowup.GraphQuasiFinite
import WeilConjectures.Blowup.InvertibleCenter
import WeilConjectures.Blowup.PartialSectionExtension
import WeilConjectures.Blowup.PartialSectionExtensionReduction
import WeilConjectures.Blowup.Principalization
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.QuasiAffineGeneral
import WeilConjectures.Blowup.QuasiAffineGeneralReduction
import WeilConjectures.Blowup.Affine.Defs
import WeilConjectures.Blowup.Affine.Projective
import WeilConjectures.Blowup.Affine.Proper
import WeilConjectures.Compactification.Affine
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.Compactification.BoundaryPreparation
import WeilConjectures.Compactification.CommonModification
import WeilConjectures.Compactification.Constructions
import WeilConjectures.Compactification.Defs
import WeilConjectures.Compactification.EliminationOfIndeterminacy
import WeilConjectures.Compactification.FinitePresentation
import WeilConjectures.Compactification.FiniteTypeDirected
import WeilConjectures.Compactification.FiniteTypeExtension
import WeilConjectures.Compactification.GraphExtension
import WeilConjectures.Compactification.IdealSheafPower
import WeilConjectures.Compactification.ImageTransport
import WeilConjectures.Compactification.IsomorphismNearClosure
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Noetherian
import WeilConjectures.Compactification.ProjectiveSpace
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Compactification.StrictTransformBlowup
import WeilConjectures.Compactification.TwoOpen
import WeilConjectures.Compactification.TwoOpenComparison
import WeilConjectures.Compactification.TwoOpenSetup
import WeilConjectures.Compactification.ValuativeCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine
import WeilConjectures.RingTheory.Dehomogenization

tex_prelude r#"
\newcommand{\Bl}{\operatorname{Bl}}
\newcommand{\Spec}{\operatorname{Spec}}
\newcommand{\Proj}{\operatorname{Proj}}
\newcommand{\sO}{\mathcal{O}}
\newcommand{\sI}{\mathcal{I}}
\newcommand{\sJ}{\mathcal{J}}
\newcommand{\sK}{\mathcal{K}}
\newcommand{\sL}{\mathcal{L}}
\newcommand{\sH}{\mathcal{H}}
\newcommand{\Aff}{\mathbb{A}}
\newcommand{\Pj}{\mathbb{P}}
\newcommand{\St}[3]{\operatorname{St}_{#3}(#1,#2)}
"#
