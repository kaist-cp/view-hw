pipeline {
    agent none

    stages {
        stage('Builds') {
            parallel {
                stage('Quick') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.11.2'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "eval `opam config env`; make -j"
                    }
                }
                stage('Full') {
                    agent {
                        docker {
                            image 'coqorg/coq:8.11.2'
                        }
                    }
                    steps {
                        sh "git submodule update --init"
                        sh "eval `opam config env`; ./build.sh"
                    }
                }
            }
        }
    }
}
