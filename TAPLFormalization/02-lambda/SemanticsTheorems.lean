import TAPLFormalization.«02-lambda».Semantics

lemma CV_NF_of_CN_NF : CN.isNF t → CV.isNF t := by
  intro t_cn_nf
  cases t_cn_nf <;> try grind [CN.isNF, CN.Neutral]
  case neutral t_cn_ne =>
    induction t_cn_ne <;> grind [CV.isNF, CV.Neutral, CN.Neutral]
  apply CV.isNF.abs
