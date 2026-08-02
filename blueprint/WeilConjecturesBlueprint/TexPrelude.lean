import VersoBlueprint

/-!
KaTeX macro prelude shared by all blueprint chapters. These are the
KaTeX-compatible definitions of the macros used throughout the blueprint.
-/

open Informal

tex_prelude r#"\newcommand{\Fq}{\mathbb{F}_q}"#
tex_prelude r#"\newcommand{\Fqn}[1]{\mathbb{F}_{q^{#1}}}"#
tex_prelude r#"\newcommand{\Fqbar}{\overline{\mathbb{F}}_q}"#
tex_prelude r#"\newcommand{\Ql}{\mathbb{Q}_\ell}"#
tex_prelude r#"\newcommand{\Qlbar}{\overline{\mathbb{Q}}_\ell}"#
tex_prelude r#"\newcommand{\ZZ}{\mathbb{Z}}"#
tex_prelude r#"\newcommand{\QQ}{\mathbb{Q}}"#
tex_prelude r#"\newcommand{\CC}{\mathbb{C}}"#
tex_prelude r#"\newcommand{\RR}{\mathbb{R}}"#
tex_prelude r#"\newcommand{\Tr}{\operatorname{Tr}}"#
tex_prelude r#"\newcommand{\Frob}{\operatorname{Frob}}"#
tex_prelude r#"\newcommand{\Spec}{\operatorname{Spec}}"#
tex_prelude r#"\newcommand{\Het}{H_{\text{ét}}}"#
tex_prelude r#"\newcommand{\Hc}{H_{c}}"#
tex_prelude r#"\newcommand{\et}[1]{#1_{\text{ét}}}"#
tex_prelude r#"\newcommand{\charrev}[1]{\det(1 - t \, #1)}"#
